import Solcore.Syntax.Internal.StatementOutcomes
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.SimpleStatementSoundness
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Internal.ControlSoundness
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Syntax.Parser.Internal.AssemblySoundness
import Solcore.Syntax.Parser.Internal.MatchSoundness
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Grammar.StatementLayer
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Grammar.Statements
import Solcore.Syntax.Parser.Internal.StatementTotality
import Solcore.Syntax.Parser.Internal.BlockSoundness

/-!
Soundness of the parsers of `for` statements and the statement layer: each success and
each rejection has its declarative derivation, and diagnostic-free runs reflect their
grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementSimpleOptionalOrdinaryOutcomeSoundnessProperties
/-! Ordinary executable outcomes for optional Core statement components. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Optional return-value success preserves the semicolon-first priority. -/
theorem optionalReturnValue_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {value : Option Expr}
    (result : optionalReturnValue expression input = .ok value output) :
    DeclarativeGrammar.OptionalReturnValueOrdinaryParses expressionOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold optionalReturnValue getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon = true
  · simp only [present, if_true, pure] at result
    cases result
    rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .statement present with
      ⟨semicolon, semicolonResult⟩
    exact .absent semicolon.span
      (symbol_ok_tokenAt .semicolon .statement semicolonResult).1
  · have absent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false] at result
    rcases bind_ok_components result with
      ⟨expressionValue, afterExpression, expressionResult, finished⟩
    cases finished
    exact .present
      (symbolAbsentAt_of_isSymbol_eq_false .semicolon absent)
      (expressionSuccessSound expressionResult)

/-- Optional return-value rejection is exactly expression rejection after a
failed semicolon guard. -/
theorem optionalReturnValue_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalReturnValue expression input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalReturnValueRejects expressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold optionalReturnValue getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon = true
  · simp [present, pure] at result
  · have absent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false] at result
    cases expressionResult : expression input with
    | invariant error => simp [expressionResult] at result
    | ok value afterExpression => simp [expressionResult, pure] at result
    | reject expressionFailure expressionRejected =>
        simp only [expressionResult] at result
        cases result
        exact .expressionRejected
          (symbolAbsentAt_of_isSymbol_eq_false .semicolon absent)
          (expressionRejectSound expressionResult)

/-- Optional let-type success uses the public ordinary Core-type outcome. -/
theorem optionalLetType_success_ordinary_sound
    {input output : State} {value : Option TypeExpr}
    (result : optionalLetType input = .ok value output) :
    DeclarativeGrammar.OptionalLetTypeParses input.declarativeRemainder value
      output.declarativeRemainder := by
  unfold optionalLetType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .colon = true
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨colon, afterColon, colonResult, typeStage⟩
    rcases bind_ok_components typeStage with
      ⟨type, afterType, typeResult, finished⟩
    cases finished
    exact .present colon.span
      (symbol_success_exactTokenParses .colon .statement colonResult)
      (typeExpr_ordinaryOutcome_sound.1 typeResult)
  · have absent : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .colon absent)

/-- Optional let-type rejection is a committed type rejection after its
exact colon. -/
theorem optionalLetType_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : optionalLetType input = .reject failure rejected) :
    DeclarativeGrammar.OptionalLetTypeRejects
      DeclarativeGrammar.TypeExprRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalLetType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .colon = true
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .colon .statement present with
      ⟨colon, colonResult⟩
    simp only [colonResult] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | ok type afterType => simp [typeResult, pure] at result
    | reject typeFailure typeRejected =>
        simp only [typeResult] at result
        cases result
        exact .typeRejected colon.span
          (symbol_success_exactTokenParses .colon .statement colonResult)
          (typeExpr_ordinaryOutcome_sound.2 typeResult)
  · have absent : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Optional let-initializer success preserves its equal guard and ordinary
expression output. -/
theorem optionalLetInitializer_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {value : Option Expr}
    (result : optionalLetInitializer expression input = .ok value output) :
    DeclarativeGrammar.OptionalLetInitializerOrdinaryParses
      expressionOrdinary input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold optionalLetInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal = true
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨equal, afterEqual, equalResult, expressionStage⟩
    rcases bind_ok_components expressionStage with
      ⟨expressionValue, afterExpression, expressionResult, finished⟩
    cases finished
    exact .present equal.span
      (symbol_success_exactTokenParses .equal .statement equalResult)
      (expressionSuccessSound expressionResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .equal absent)

/-- Optional let-initializer rejection is a committed expression rejection
after its exact equal marker. -/
theorem optionalLetInitializer_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalLetInitializer expression input =
      .reject failure rejected) :
    DeclarativeGrammar.OptionalLetInitializerRejects expressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold optionalLetInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal = true
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .equal .statement present with
      ⟨equal, equalResult⟩
    simp only [equalResult] at result
    cases expressionResult : expression
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [expressionResult] at result
    | ok value afterExpression =>
        simp [expressionResult, pure] at result
    | reject expressionFailure expressionRejected =>
        simp only [expressionResult] at result
        cases result
        exact .expressionRejected equal.span
          (symbol_success_exactTokenParses .equal .statement equalResult)
          (expressionRejectSound expressionResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end Solcore.Syntax.Parser.StatementSimpleInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementSimpleOrdinarySuccessSoundnessProperties
/-! Ordinary executable success for canonical Core `let` and `return`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable `let` success records its exact marker, checked name,
optional type, optional initializer, semicolon, AST, span, and remainder. -/
theorem letStatement_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {statement : Statement}
    (result : letStatement expression input = .ok statement output) :
    DeclarativeGrammar.LetStatementOrdinaryParses expressionOrdinary
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold letStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, typeStage⟩
  rcases bind_ok_components typeStage with
    ⟨type, afterType, typeResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed marker.span semicolon.span
    (keyword_success_exactTokenParses .letKw .statement markerResult)
    (identifier_success_sound .statement nameResult)
    (StatementSimpleInternals.optionalLetType_success_ordinary_sound
      typeResult)
    (StatementSimpleInternals.optionalLetInitializer_success_ordinary_sound
      expression expressionOrdinary expressionSuccessSound initializerResult)
    (symbol_success_exactTokenParses .semicolon .statement semicolonResult)

/-- Every executable `return` success records the semicolon-prioritized
optional value, exact terminator, AST, span, and remainder. -/
theorem returnStatement_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {statement : Statement}
    (result : returnStatement expression input = .ok statement output) :
    DeclarativeGrammar.ReturnStatementOrdinaryParses expressionOrdinary
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold returnStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, valueStage⟩
  rcases bind_ok_components valueStage with
    ⟨value, afterValue, valueResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed marker.span semicolon.span
    (keyword_success_exactTokenParses .returnKw .statement markerResult)
    (StatementSimpleInternals.optionalReturnValue_success_ordinary_sound
      expression expressionOrdinary expressionSuccessSound valueResult)
    (symbol_success_exactTokenParses .semicolon .statement semicolonResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementSimpleOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection for canonical Core `let` and `return`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable `let` rejection records the first failing stage and its
exact rejected remainder. -/
theorem letStatement_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : letStatement expression input = .reject failure rejected) :
    DeclarativeGrammar.LetStatementRejects expressionOrdinary
      expressionRejects DeclarativeGrammar.TypeExprRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  unfold letStatement at result
  cases markerResult : keyword .letKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq .letKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerRejected
        (keyword_reject_tokenKindAbsentAt .letKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .letKw .statement
        markerResult
      cases nameResult : identifier .statement afterMarker with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected marker.span markerParsed
            (identifier_reject_sound .statement nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .statement nameResult
          cases typeResult : StatementSimpleInternals.optionalLetType afterName
              with
          | invariant error => simp [typeResult] at result
          | reject typeFailure typeRejected =>
              simp only [typeResult] at result
              cases result
              exact .typeRejected marker.span markerParsed nameParsed
                (StatementSimpleInternals.optionalLetType_reject_ordinary_sound
                  typeResult)
          | ok type afterType =>
              simp only [typeResult] at result
              have typeParsed :=
                StatementSimpleInternals.optionalLetType_success_ordinary_sound
                  typeResult
              cases initializerResult :
                  StatementSimpleInternals.optionalLetInitializer expression
                    afterType with
              | invariant error => simp [initializerResult] at result
              | reject initializerFailure initializerRejected =>
                  simp only [initializerResult] at result
                  cases result
                  exact .initializerRejected marker.span markerParsed
                    nameParsed typeParsed
                    (StatementSimpleInternals.optionalLetInitializer_reject_ordinary_sound
                      expression expressionRejects expressionRejectSound
                        initializerResult)
              | ok initializer afterInitializer =>
                  simp only [initializerResult] at result
                  have initializerParsed :=
                    StatementSimpleInternals.optionalLetInitializer_success_ordinary_sound
                      expression expressionOrdinary expressionSuccessSound
                        initializerResult
                  cases semicolonResult : symbol .semicolon .statement
                      afterInitializer with
                  | invariant error => simp [semicolonResult] at result
                  | ok semicolon output =>
                      simp [semicolonResult, pure] at result
                  | reject semicolonFailure semicolonRejected =>
                      have semicolonRejectedEq := symbol_reject_state_eq
                        .semicolon .statement semicolonResult
                      subst semicolonRejected
                      simp only [semicolonResult] at result
                      cases result
                      exact .semicolonRejected marker.span markerParsed
                        nameParsed typeParsed initializerParsed
                        (symbol_reject_tokenKindAbsentAt .semicolon .statement
                          semicolonResult)

/-- Every executable `return` rejection records marker, optional-value, or
required-semicolon failure in parser priority order. -/
theorem returnStatement_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : returnStatement expression input = .reject failure rejected) :
    DeclarativeGrammar.ReturnStatementRejects expressionOrdinary
      expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold returnStatement at result
  cases markerResult : keyword .returnKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq .returnKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerRejected
        (keyword_reject_tokenKindAbsentAt .returnKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .returnKw
        .statement markerResult
      cases valueResult : StatementSimpleInternals.optionalReturnValue
          expression afterMarker with
      | invariant error => simp [valueResult] at result
      | reject valueFailure valueRejected =>
          simp only [valueResult] at result
          cases result
          exact .valueRejected marker.span markerParsed
            (StatementSimpleInternals.optionalReturnValue_reject_ordinary_sound
              expression expressionRejects expressionRejectSound valueResult)
      | ok value afterValue =>
          simp only [valueResult] at result
          have valueParsed :=
            StatementSimpleInternals.optionalReturnValue_success_ordinary_sound
              expression expressionOrdinary expressionSuccessSound valueResult
          cases semicolonResult : symbol .semicolon .statement afterValue with
          | invariant error => simp [semicolonResult] at result
          | ok semicolon output => simp [semicolonResult, pure] at result
          | reject semicolonFailure semicolonRejected =>
              have semicolonRejectedEq := symbol_reject_state_eq .semicolon
                .statement semicolonResult
              subst semicolonRejected
              simp only [semicolonResult] at result
              cases result
              exact .semicolonRejected marker.span markerParsed valueParsed
                (symbol_reject_tokenKindAbsentAt .semicolon .statement
                  semicolonResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementSimpleOrdinaryOutcomeSoundnessProperties
/-! Packaged ordinary outcomes for canonical Core `let` and `return`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable Core `let` success and exact rejection. -/
theorem letStatement_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {statement : Statement},
      letStatement expression input = .ok statement output →
        DeclarativeGrammar.LetStatementOrdinaryParses expressionOrdinary
          input.declarativeRemainder statement output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      letStatement expression input = .reject failure rejected →
        DeclarativeGrammar.LetStatementRejects expressionOrdinary
          expressionRejects DeclarativeGrammar.TypeExprRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨letStatement_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    letStatement_reject_ordinary_sound expression expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic Core `let` outcomes with the fixed public Core
type outcome. -/
theorem letStatement_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LetStatementOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.LetStatementRejects expressionOrdinary
        expressionRejects DeclarativeGrammar.TypeExprRejects) :=
  DeclarativeGrammar.letStatementDeterministicOutcomeSpec expressionOutcomes
    DeclarativeGrammar.typeExprDeterministicOutcomeSpec

/-- Package executable Core `return` success and exact rejection. -/
theorem returnStatement_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {statement : Statement},
      returnStatement expression input = .ok statement output →
        DeclarativeGrammar.ReturnStatementOrdinaryParses expressionOrdinary
          input.declarativeRemainder statement output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      returnStatement expression input = .reject failure rejected →
        DeclarativeGrammar.ReturnStatementRejects expressionOrdinary
          expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨returnStatement_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    returnStatement_reject_ordinary_sound expression expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic Core `return` outcomes. -/
theorem returnStatement_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ReturnStatementOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ReturnStatementRejects expressionOrdinary
        expressionRejects) :=
  DeclarativeGrammar.returnStatementDeterministicOutcomeSpec
    expressionOutcomes

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemOrdinarySuccessSoundnessProperties
/-! Ordinary executable success for one Core `for`-header item. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace StatementSimpleInternals

/-- Executable `for let` success follows the diagnostic-inclusive ordinary
grammar with the fixed public Core type outcome. -/
theorem forLetItem_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {item : ForItem}
    (result : forLetItem expression input = .ok item output) :
    DeclarativeGrammar.ForLetItemOrdinaryParses expressionOrdinary
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold forLetItem at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, typeStage⟩
  rcases bind_ok_components typeStage with
    ⟨type, afterType, typeResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .letKw .statement markerResult)
    (identifier_success_sound .statement nameResult)
    (optionalLetType_success_ordinary_sound typeResult)
    (optionalLetInitializer_success_ordinary_sound expression
      expressionOrdinary expressionSuccessSound initializerResult)

/-- Executable fallback success preserves the initial expression, maximal
optional assignment tail, AST, span, and final remainder. -/
theorem forAssignmentOrExpression_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {item : ForItem}
    (result : forAssignmentOrExpression expression input = .ok item output) :
    DeclarativeGrammar.ForAssignmentOrExpressionOrdinaryParses
      expressionOrdinary input.declarativeRemainder item
        output.declarativeRemainder := by
  unfold forAssignmentOrExpression at result
  rcases bind_ok_components result with
    ⟨left, afterLeft, leftResult, tailStage⟩
  rcases bind_ok_components tailStage with
    ⟨tail, afterTail, tailResult, finished⟩
  have leftParsed := expressionSuccessSound leftResult
  have tailParsed := optionalAssignmentTail_success_ordinary_sound expression
    expressionOrdinary expressionSuccessSound tailResult
  cases tail with
  | none =>
      cases finished
      exact ⟨left, afterLeft.declarativeRemainder, none, leftParsed,
        tailParsed, .expression left⟩
  | some tail =>
      cases tail with
      | value operator right =>
          cases finished
          exact ⟨left, afterLeft.declarativeRemainder,
            some (.value operator right), leftParsed, tailParsed,
            .value left right operator⟩
      | bitNot operator =>
          cases finished
          exact ⟨left, afterLeft.declarativeRemainder,
            some (.bitNot operator), leftParsed, tailParsed,
            .bitNot left operator⟩

end StatementSimpleInternals

/-- The public dispatcher commits to `let` exactly when its guard succeeds. -/
theorem forItem_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    {input output : State} {item : ForItem}
    (result : forItem expression input = .ok item output) :
    DeclarativeGrammar.ForItemOrdinaryParses expressionOrdinary
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold forItem at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    exact .letItem
      (StatementSimpleInternals.forLetItem_success_ordinary_sound expression
        expressionOrdinary expressionSuccessSound result)
  · have letAbsent : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letAbsent, Bool.false_eq_true, if_false] at result
    exact .assignmentOrExpression
      (keywordAbsentAt_of_isKeyword_eq_false .letKw letAbsent)
      (StatementSimpleInternals.forAssignmentOrExpression_success_ordinary_sound
        expression expressionOrdinary expressionSuccessSound result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemsTailOrdinarySuccessSoundnessProperties
/-! Executable ordinary success for reverse-accumulating Core `for` tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- The executable reverse accumulator is the returned prefix, followed by
the exact forward suffix parsed from the current state. -/
theorem forItemsTail_success_ordinary_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder) :
    ∀ fuel itemsRev input items output,
      forItemsTail expression stop fuel itemsRev input = .ok items output →
      ∃ suffix,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.ForItemsTailOrdinaryParses expressionOrdinary stop
          input.declarativeRemainder suffix output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items output result
      simp [forItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input items output result
      unfold forItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp only [commaPresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (symbolAbsentAt_of_isSymbol_eq_false .comma commaPresent)⟩
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .statement input with
          | invariant error => simp [commaResult] at result
          | reject failure rejected => simp [commaResult] at result
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases stopPresent : isSymbol afterComma stop with
              | true =>
                  simp only [stopPresent, if_true] at result
                  unfold rejectAt at result
                  contradiction
              | false =>
                  simp only [stopPresent, Bool.false_eq_true, if_false]
                    at result
                  cases itemResult : forItem expression afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject failure rejected => simp [itemResult] at result
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      by_cases progress : afterItem.cursor > afterComma.cursor
                      · simp only [progress, if_true] at result
                        rcases inductionHypothesis (item :: itemsRev)
                            afterItem items output result with
                          ⟨suffix, itemsEq, tailParsed⟩
                        refine ⟨item :: suffix, ?_,
                          .next comma.span
                            (symbol_success_exactTokenParses .comma .statement
                              commaResult)
                            (symbolAbsentAt_of_isSymbol_eq_false stop
                              stopPresent)
                            (forItem_success_ordinary_sound expression
                              expressionOrdinary expressionSuccessSound
                                itemResult)
                            (by simpa [State.declarativeRemainder] using
                              progress)
                            tailParsed⟩
                        simpa [List.reverse_cons, List.append_assoc] using
                          itemsEq
                      · simp only [progress, if_false] at result
                        contradiction

end Solcore.Syntax.Parser.ControlInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection for one Core `for`-header item. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

/-- Executable `for let` rejection identifies the first rejected stage. -/
theorem forLetItem_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : forLetItem expression input = .reject failure rejected) :
    DeclarativeGrammar.ForLetItemRejects expressionOrdinary
      expressionRejects DeclarativeGrammar.TypeExprRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  unfold forLetItem at result
  cases markerResult : keyword .letKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := keyword_reject_state_eq .letKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerRejected
        (keyword_reject_tokenKindAbsentAt .letKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .letKw .statement
        markerResult
      cases nameResult : identifier .statement afterMarker with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected marker.span markerParsed
            (identifier_reject_sound .statement nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .statement nameResult
          cases typeResult : optionalLetType afterName with
          | invariant error => simp [typeResult] at result
          | reject typeFailure typeRejected =>
              simp only [typeResult] at result
              cases result
              exact .typeRejected marker.span markerParsed nameParsed
                (optionalLetType_reject_ordinary_sound typeResult)
          | ok type afterType =>
              simp only [typeResult] at result
              have typeParsed := optionalLetType_success_ordinary_sound
                typeResult
              cases initializerResult : optionalLetInitializer expression
                  afterType with
              | invariant error => simp [initializerResult] at result
              | reject initializerFailure initializerRejected =>
                  simp only [initializerResult] at result
                  cases result
                  exact .initializerRejected marker.span markerParsed
                    nameParsed typeParsed
                    (optionalLetInitializer_reject_ordinary_sound expression
                      expressionRejects expressionRejectSound
                        initializerResult)
              | ok initializer afterInitializer =>
                  simp [initializerResult, pure] at result

/-- The fallback can reject only in its initial expression or the right side
of a committed value-assignment suffix. -/
theorem forAssignmentOrExpression_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : forAssignmentOrExpression expression input =
      .reject failure rejected) :
    DeclarativeGrammar.ForAssignmentOrExpressionRejects expressionOrdinary
      expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold forAssignmentOrExpression at result
  cases leftResult : expression input with
  | invariant error => simp [bind, leftResult] at result
  | reject leftFailure leftRejected =>
      simp only [bind, leftResult] at result
      cases result
      exact .leftRejected (expressionRejectSound leftResult)
  | ok left afterLeft =>
      simp only [bind, leftResult] at result
      have leftParsed := expressionSuccessSound leftResult
      cases tailResult : optionalAssignmentTail expression afterLeft with
      | invariant error => simp [tailResult] at result
      | reject tailFailure tailRejected =>
          simp only [tailResult] at result
          rcases optionalAssignmentTail_reject_ordinary_sound expression
              expressionRejects expressionRejectSound tailResult with
            ⟨afterOperator, operator, tildeAbsent, operatorParsed,
              rightRejected⟩
          cases result
          exact .rightRejected leftParsed tildeAbsent operatorParsed
            rightRejected
      | ok tail afterTail =>
          cases tail with
          | none => simp [tailResult, pure] at result
          | some tail => cases tail <;> simp [tailResult, pure] at result

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

/-- Public rejection follows the same positive-`let` commitment as the
executable dispatcher and carries exact negative evidence on fallback. -/
theorem forItem_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : forItem expression input = .reject failure rejected) :
    DeclarativeGrammar.ForItemRejects expressionOrdinary expressionRejects
      DeclarativeGrammar.TypeExprRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold forItem at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    rcases keyword_eq_ok_of_isKeyword_eq_true .letKw .statement letPresent
      with ⟨marker, markerResult⟩
    exact .letItem
      (keyword_success_exactTokenParses .letKw .statement markerResult).1
      (StatementSimpleInternals.forLetItem_reject_ordinary_sound expression
        expressionOrdinary expressionRejects expressionRejectSound result)
  · have letAbsent : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letAbsent, Bool.false_eq_true, if_false] at result
    exact .assignmentOrExpression
      (keywordAbsentAt_of_isKeyword_eq_false .letKw letAbsent)
      (StatementSimpleInternals.forAssignmentOrExpression_reject_ordinary_sound
        expression expressionOrdinary expressionRejects
          expressionSuccessSound expressionRejectSound result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemOrdinaryOutcomeSoundnessProperties
/-! Packaged ordinary outcomes for one Core `for`-header item. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

/-- Package executable `for let` success and exact rejection. -/
theorem forLetItem_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {item : ForItem},
      forLetItem expression input = .ok item output →
        DeclarativeGrammar.ForLetItemOrdinaryParses expressionOrdinary
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forLetItem expression input = .reject failure rejected →
        DeclarativeGrammar.ForLetItemRejects expressionOrdinary
          expressionRejects DeclarativeGrammar.TypeExprRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨forLetItem_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    forLetItem_reject_ordinary_sound expression expressionOrdinary
      expressionRejects expressionRejectSound⟩

/-- Re-export deterministic `for let` outcomes with the fixed public Core
type outcome. -/
theorem forLetItem_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForLetItemOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ForLetItemRejects expressionOrdinary
        expressionRejects DeclarativeGrammar.TypeExprRejects) :=
  DeclarativeGrammar.forLetItemDeterministicOutcomeSpec expressionOutcomes
    DeclarativeGrammar.typeExprDeterministicOutcomeSpec

/-- Package executable assignment/expression-item success and rejection. -/
theorem forAssignmentOrExpression_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {item : ForItem},
      forAssignmentOrExpression expression input = .ok item output →
        DeclarativeGrammar.ForAssignmentOrExpressionOrdinaryParses
          expressionOrdinary input.declarativeRemainder item
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forAssignmentOrExpression expression input = .reject failure rejected →
        DeclarativeGrammar.ForAssignmentOrExpressionRejects
          expressionOrdinary expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨forAssignmentOrExpression_success_ordinary_sound expression
      expressionOrdinary expressionSuccessSound,
    forAssignmentOrExpression_reject_ordinary_sound expression
      expressionOrdinary expressionRejects expressionSuccessSound
        expressionRejectSound⟩

/-- Re-export deterministic fallback-item outcomes. -/
theorem forAssignmentOrExpression_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForAssignmentOrExpressionOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.ForAssignmentOrExpressionRejects
        expressionOrdinary expressionRejects) :=
  DeclarativeGrammar.forAssignmentOrExpressionDeterministicOutcomeSpec
    expressionOutcomes

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

/-- Package both outcomes of the executable let-prioritized dispatcher. -/
theorem forItem_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {item : ForItem},
      forItem expression input = .ok item output →
        DeclarativeGrammar.ForItemOrdinaryParses expressionOrdinary
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forItem expression input = .reject failure rejected →
        DeclarativeGrammar.ForItemRejects expressionOrdinary
          expressionRejects DeclarativeGrammar.TypeExprRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨forItem_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    forItem_reject_ordinary_sound expression expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic public-item outcomes. -/
theorem forItem_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForItemOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ForItemRejects expressionOrdinary
        expressionRejects DeclarativeGrammar.TypeExprRejects) :=
  DeclarativeGrammar.forItemDeterministicOutcomeSpec expressionOutcomes
    DeclarativeGrammar.typeExprDeterministicOutcomeSpec

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemsTailOrdinaryRejectionSoundnessProperties
/-! Executable exact rejection for Core `for` item-list tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

private theorem symbolTokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .statement present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .statement parsed).1⟩

/-- Every executable tail rejection records the committed comma, stop-after-
comma error, rejected item, or recursively rejected suffix. -/
theorem forItemsTail_reject_ordinary_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    ∀ fuel itemsRev input failure rejected,
      forItemsTail expression stop fuel itemsRev input =
          .reject failure rejected →
      DeclarativeGrammar.ForItemsTailRejects expressionOrdinary
        expressionRejects stop input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input failure rejected result
      simp [forItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input failure rejected result
      unfold forItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp [commaPresent] at result
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .statement input with
          | invariant error => simp [commaResult] at result
          | reject commaFailure commaRejected =>
              rcases symbol_eq_ok_of_isSymbol_eq_true .comma .statement
                commaPresent with ⟨comma, parsed⟩
              rw [parsed] at commaResult
              contradiction
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases stopPresent : isSymbol afterComma stop with
              | true =>
                  simp only [stopPresent, if_true] at result
                  rcases symbolTokenAt_of_isSymbol_eq_true stop stopPresent with
                    ⟨stopSpan, stopCurrent⟩
                  unfold rejectAt at result
                  cases result
                  exact .stopAfterComma comma.span stopSpan
                    (symbol_success_exactTokenParses .comma .statement
                      commaResult)
                    stopCurrent
              | false =>
                  simp only [stopPresent, Bool.false_eq_true, if_false]
                    at result
                  cases itemResult : forItem expression afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject itemFailure itemRejected =>
                      simp only [itemResult] at result
                      cases result
                      exact .itemRejected comma.span
                        (symbol_success_exactTokenParses .comma .statement
                          commaResult)
                        (symbolAbsentAt_of_isSymbol_eq_false stop stopPresent)
                        (forItem_reject_ordinary_sound expression
                          expressionOrdinary expressionRejects
                            expressionSuccessSound expressionRejectSound
                              itemResult)
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      by_cases progress : afterItem.cursor > afterComma.cursor
                      · simp only [progress, if_true] at result
                        exact .laterRejected comma.span
                          (symbol_success_exactTokenParses .comma .statement
                            commaResult)
                          (symbolAbsentAt_of_isSymbol_eq_false stop
                            stopPresent)
                          (forItem_success_ordinary_sound expression
                            expressionOrdinary expressionSuccessSound
                              itemResult)
                          (by simpa [State.declarativeRemainder] using
                            progress)
                          (inductionHypothesis (item :: itemsRev) afterItem
                            failure rejected result)
                      · simp only [progress, if_false] at result
                        contradiction

end Solcore.Syntax.Parser.ControlInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemsTailOrdinaryOutcomeSoundnessProperties
/-! Packaged executable ordinary outcomes for Core `for` item-list tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Package success with reverse-accumulator order and exact tail rejection. -/
theorem forItemsTail_ordinaryOutcome_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ fuel itemsRev input items output,
      forItemsTail expression stop fuel itemsRev input = .ok items output →
        ∃ suffix,
          items = itemsRev.reverse ++ suffix ∧
          DeclarativeGrammar.ForItemsTailOrdinaryParses expressionOrdinary
            stop input.declarativeRemainder suffix
              output.declarativeRemainder) ∧
    (∀ fuel itemsRev input failure rejected,
      forItemsTail expression stop fuel itemsRev input =
          .reject failure rejected →
        DeclarativeGrammar.ForItemsTailRejects expressionOrdinary
          expressionRejects stop input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨forItemsTail_success_ordinary_sound expression stop expressionOrdinary
      expressionSuccessSound,
    forItemsTail_reject_ordinary_sound expression stop expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic Core `for` tail outcomes. -/
theorem forItemsTail_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) (stop : Symbol) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForItemsTailOrdinaryParses expressionOrdinary stop)
      (DeclarativeGrammar.ForItemsTailRejects expressionOrdinary
        expressionRejects stop) :=
  DeclarativeGrammar.forItemsTailDeterministicOutcomeSpec expressionOutcomes
    stop

end Solcore.Syntax.Parser.ControlInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementFallbackDiagnosticProperties
/-!
Diagnostic commitment at the recognized-statement fallback boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- A diagnostic-free success of recognized-statement choice is exactly the
unchanged success of the recognized primary branch.  A fallback success after
primary rejection necessarily commits the primary failure diagnostic. -/
theorem recognizedStatementOrFallback_primary_of_diagnosticFree_success
    (primary fallback : Parser Statement)
    {input next : State} {value : Statement}
    (result : recognizedStatementOrFallback primary fallback input =
      .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    primary input = .ok value next := by
  unfold recognizedStatementOrFallback at result
  cases primaryResult : primary input with
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState =>
          simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          cases result
          simp [State.emit] at diagnosticFree
  | invariant error => simp [primaryResult] at result

/-- Diagnostic reflection for recognized-statement choice reduces to the
primary parser on every diagnostic-free success. -/
theorem recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
    (primary fallback : Parser Statement)
    (primaryReflects : Parser.ReflectsDiagnosticFreeOnSuccess primary) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (recognizedStatementOrFallback primary fallback) := by
  intro input value next result diagnosticFree
  exact primaryReflects input value next
    (recognizedStatementOrFallback_primary_of_diagnosticFree_success
      primary fallback result diagnosticFree)
    diagnosticFree

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementLayerDiagnosticReflectionProperties
/-! Diagnostic reflection for the prioritized Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- The full statement layer cannot erase diagnostics on successful parsing. -/
theorem statementLayer_reflectsDiagnosticFreeOnSuccess
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nestedStatement)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern)
    (yulBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess yulBody) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (statementLayer nestedStatement expression pattern) := by
  intro input value next result diagnosticFree
  unfold statementLayer at result
  split at result
  · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
      (letStatement expression) (assignmentOrExpressionStatement expression)
        (letStatement_reflectsDiagnosticFreeOnSuccess expression
          expressionReflects) input value next result diagnosticFree
  · split at result
    · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
        (returnStatement expression)
          (assignmentOrExpressionStatement expression)
          (returnStatement_reflectsDiagnosticFreeOnSuccess expression
            expressionReflects) input value next result diagnosticFree
    · split at result
      · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
          (matchStatement nestedStatement expression pattern)
            (assignmentOrExpressionStatement expression)
            (matchStatement_reflectsDiagnosticFreeOnSuccess nestedStatement
              expression pattern nestedReflects expressionReflects
                patternReflects) input value next result diagnosticFree
      · split at result
        · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
            (forStatement nestedStatement expression)
              (assignmentOrExpressionStatement expression)
              (forStatement_reflectsDiagnosticFreeOnSuccess nestedStatement
                expression nestedReflects expressionReflects) input value next
                  result diagnosticFree
        · split at result
          · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
              (whileStatement nestedStatement expression)
                (assignmentOrExpressionStatement expression)
                (whileStatement_reflectsDiagnosticFreeOnSuccess
                  nestedStatement expression nestedReflects expressionReflects)
                    input value next result diagnosticFree
          · split at result
            · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                (ifStatement nestedStatement expression)
                  (assignmentOrExpressionStatement expression)
                  (ifStatement_reflectsDiagnosticFreeOnSuccess nestedStatement
                    expression nestedReflects expressionReflects) input value
                      next result diagnosticFree
            · split at result
              · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                  assemblyStatement (assignmentOrExpressionStatement expression)
                    (assemblyStatement_reflectsDiagnosticFreeOnSuccess
                      yulBodyReflects) input value next result diagnosticFree
              · split at result
                · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                    (blockStatement nestedStatement)
                      (assignmentOrExpressionStatement expression)
                      (blockStatement_reflectsDiagnosticFreeOnSuccess
                        nestedStatement nestedReflects) input value next result
                          diagnosticFree
                · split at result
                  · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                      breakStatement (assignmentOrExpressionStatement expression)
                        breakStatement_reflectsDiagnosticFreeOnSuccess input
                          value next result diagnosticFree
                  · split at result
                    · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                        continueStatement
                          (assignmentOrExpressionStatement expression)
                          continueStatement_reflectsDiagnosticFreeOnSuccess
                            input value next result diagnosticFree
                    · exact
                        assignmentOrExpressionStatement_reflectsDiagnosticFreeOnSuccess
                          expression expressionReflects input value next result
                            diagnosticFree

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.RecognizedCoreStatementFallbackOutcomeProperties
/-! Executable outcome bridges for recognized Core-statement fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every Core wrapper success follows the preferred ordinary relation or an
exact preferred rejection followed by fallback success at the original
input. -/
theorem TermInternals.recognizedStatementOrFallback_success_ordinary_sound
    (primary fallback : Parser Statement)
    (primaryParses fallbackParses :
      DeclarativeGrammar.Remainder → Statement →
        DeclarativeGrammar.Remainder → Prop)
    (primaryRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primarySuccessSound : ∀ {input output : State} {value : Statement},
      primary input = .ok value output →
        primaryParses input.declarativeRemainder value
          output.declarativeRemainder)
    (primaryRejectSound : ∀ {input rejected : State} {failure : Failure},
      primary input = .reject failure rejected →
        primaryRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (fallbackSuccessSound : ∀ {input output : State} {value : Statement},
      fallback input = .ok value output →
        fallbackParses input.declarativeRemainder value
          output.declarativeRemainder)
    {input output : State} {value : Statement}
    (result : TermInternals.recognizedStatementOrFallback primary fallback
      input = .ok value output) :
    DeclarativeGrammar.TransactionalFallbackOrdinaryParses primaryParses
      primaryRejects fallbackParses input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold TermInternals.recognizedStatementOrFallback at result
  cases primaryResult : primary input with
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      cases result
      exact .primary (primarySuccessSound primaryResult)
  | invariant error => simp [primaryResult] at result
  | reject primaryFailure primaryRejected =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackRejected =>
          simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          let reset : State := {
            afterFallback with diagnosticsRev := input.diagnosticsRev
          }
          have parsed :
              DeclarativeGrammar.TransactionalFallbackOrdinaryParses
                primaryParses primaryRejects fallbackParses
                input.declarativeRemainder fallbackValue
                  afterFallback.declarativeRemainder :=
            .fallback (primaryRejectSound primaryResult)
              (fallbackSuccessSound fallbackResult)
          change Reply.ok fallbackValue
            (reset.emit primaryFailure.toDiagnostic) = .ok value output
              at result
          cases result
          simpa [reset, State.emit, State.declarativeRemainder] using parsed

/-- A Core wrapper rejection decomposes into both branch rejections and the
original returned input state. -/
theorem TermInternals.recognizedStatementOrFallback_reject_decomposition
    (primary fallback : Parser Statement)
    {input rejected : State} {failure : Failure}
    (result : TermInternals.recognizedStatementOrFallback primary fallback
      input = .reject failure rejected) :
    ∃ primaryRejected fallbackFailure fallbackRejected,
      primary input = .reject failure primaryRejected ∧
        fallback input = .reject fallbackFailure fallbackRejected ∧
        rejected = input := by
  unfold TermInternals.recognizedStatementOrFallback at result
  cases primaryResult : primary input with
  | ok primaryValue afterPrimary => simp [primaryResult] at result
  | invariant error => simp [primaryResult] at result
  | reject primaryFailure primaryRejected =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | ok fallbackValue afterFallback => simp [fallbackResult] at result
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackRejected =>
          simp only [fallbackResult] at result
          cases result
          exact ⟨primaryRejected, fallbackFailure, fallbackRejected,
            rfl, rfl, rfl⟩

/-- Every Core wrapper rejection follows the exact both-rejected relation and
is nonconsuming. -/
theorem TermInternals.recognizedStatementOrFallback_reject_sound
    (primary fallback : Parser Statement)
    (primaryRejects fallbackRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primaryRejectSound : ∀ {input rejected : State} {failure : Failure},
      primary input = .reject failure rejected →
        primaryRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (fallbackRejectSound : ∀ {input rejected : State} {failure : Failure},
      fallback input = .reject failure rejected →
        fallbackRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : TermInternals.recognizedStatementOrFallback primary fallback
      input = .reject failure rejected) :
    DeclarativeGrammar.TransactionalFallbackRejects primaryRejects
      fallbackRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  rcases TermInternals.recognizedStatementOrFallback_reject_decomposition
      primary fallback result with
    ⟨primaryRejected, fallbackFailure, fallbackRejected, primaryResult,
      fallbackResult, rejectedEq⟩
  subst rejected
  exact .both (primaryRejectSound primaryResult)
    (fallbackRejectSound fallbackResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.RecognizedCoreStatementFallbackOrdinaryOutcomeSoundnessProperties
/-! Packaged ordinary outcomes for recognized Core-statement fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Package executable success and rejection of one recognized branch with
transactional fallback at the original input. -/
theorem recognizedStatementOrFallback_ordinaryOutcome_sound
    (primary fallback : Parser Statement)
    (primaryParses fallbackParses :
      DeclarativeGrammar.Remainder → Statement →
        DeclarativeGrammar.Remainder → Prop)
    (primaryRejects fallbackRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primarySuccessSound : ∀ {input output : State} {value : Statement},
      primary input = .ok value output → primaryParses
        input.declarativeRemainder value output.declarativeRemainder)
    (primaryRejectSound : ∀ {input rejected : State} {failure : Failure},
      primary input = .reject failure rejected → primaryRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (fallbackSuccessSound : ∀ {input output : State} {value : Statement},
      fallback input = .ok value output → fallbackParses
        input.declarativeRemainder value output.declarativeRemainder)
    (fallbackRejectSound : ∀ {input rejected : State} {failure : Failure},
      fallback input = .reject failure rejected → fallbackRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {value : Statement},
      recognizedStatementOrFallback primary fallback input =
          .ok value output →
        DeclarativeGrammar.TransactionalFallbackOrdinaryParses primaryParses
          primaryRejects fallbackParses input.declarativeRemainder value
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recognizedStatementOrFallback primary fallback input =
          .reject failure rejected →
        DeclarativeGrammar.TransactionalFallbackRejects primaryRejects
          fallbackRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨recognizedStatementOrFallback_success_ordinary_sound primary fallback
      primaryParses fallbackParses primaryRejects primarySuccessSound
        primaryRejectSound fallbackSuccessSound,
    recognizedStatementOrFallback_reject_sound primary fallback
      primaryRejects fallbackRejects primaryRejectSound fallbackRejectSound⟩

/-- Lift deterministic primary and fallback outcomes through the executable
transactional wrapper relation. -/
theorem recognizedStatementOrFallback_ordinaryOutcomeSpec
    (primaryParses fallbackParses :
      DeclarativeGrammar.Remainder → Statement →
        DeclarativeGrammar.Remainder → Prop)
    (primaryRejects fallbackRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (primaryOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      primaryParses primaryRejects)
    (fallbackOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      fallbackParses fallbackRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.TransactionalFallbackOrdinaryParses primaryParses
        primaryRejects fallbackParses)
      (DeclarativeGrammar.TransactionalFallbackRejects primaryRejects
        fallbackRejects) :=
  DeclarativeGrammar.transactionalFallbackDeterministicOutcomeSpec
    primaryParses fallbackParses primaryRejects fallbackRejects
      primaryOutcomes fallbackOutcomes

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementLayerOrdinarySuccessHelperProperties
/-! Shared guarded-success machinery for the Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals.StatementLayerSuccessInternals

theorem keyword_guard_of_true (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .statement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .statement result).1⟩

theorem contextual_guard_of_true (value : ContextualKeyword)
    {input : State} (present : isContextual input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.identifier value.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true value .statement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses value .statement result).1⟩

theorem symbol_guard_of_true (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .statement present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .statement result).1⟩

theorem selected_guarded_success
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expression : Parser Expr)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (stage : DeclarativeGrammar.StatementLayerStage)
    (notFallback : stage ≠ .fallback)
    {input output : State} {value : Statement}
    (priority : DeclarativeGrammar.StatementLayerPrefixAbsent
      input.declarativeRemainder stage)
    (guard : DeclarativeGrammar.StatementLayerGuardAt
      input.declarativeRemainder stage)
    (primary : Parser Statement)
    (primaryOutcome :
      (∀ {branchInput branchOutput : State} {branchValue : Statement},
        primary branchInput = .ok branchValue branchOutput →
          DeclarativeGrammar.StatementLayerPrimaryOrdinaryParses
            statementOrdinary expressionOrdinary patternOrdinary stage
              branchInput.declarativeRemainder branchValue
                branchOutput.declarativeRemainder) ∧
      (∀ {branchInput branchRejected : State} {failure : Failure},
        primary branchInput = .reject failure branchRejected →
          DeclarativeGrammar.StatementLayerPrimaryRejects statementOrdinary
            statementRejects expressionOrdinary expressionRejects
              patternOrdinary patternRejects stage
                branchInput.declarativeRemainder
                  branchRejected.declarativeRemainder))
    (result : recognizedStatementOrFallback primary
      (assignmentOrExpressionStatement expression) input = .ok value output) :
    DeclarativeGrammar.StatementLayerOrdinaryParses statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder value
          output.declarativeRemainder := by
  have fallbackSuccess : ∀ {fallbackInput fallbackOutput : State}
      {fallbackValue : Statement},
      assignmentOrExpressionStatement expression fallbackInput =
          .ok fallbackValue fallbackOutput →
        DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
          expressionOrdinary fallbackInput.declarativeRemainder fallbackValue
            fallbackOutput.declarativeRemainder :=
    assignmentOrExpressionStatement_success_ordinary_sound expression
      expressionOrdinary expressionSuccessSound
  have fallbackReject : ∀ {fallbackInput fallbackRejected : State}
      {failure : Failure},
      assignmentOrExpressionStatement expression fallbackInput =
          .reject failure fallbackRejected →
        DeclarativeGrammar.AssignmentOrExpressionStatementRejects
          expressionOrdinary expressionRejects
            fallbackInput.declarativeRemainder
              fallbackRejected.declarativeRemainder :=
    assignmentOrExpressionStatement_reject_ordinary_sound expression
      expressionOrdinary expressionRejects expressionSuccessSound
        expressionRejectSound
  exact ⟨stage, .guarded notFallback priority guard
    ((recognizedStatementOrFallback_ordinaryOutcome_sound primary
      (assignmentOrExpressionStatement expression)
      (DeclarativeGrammar.StatementLayerPrimaryOrdinaryParses
        statementOrdinary expressionOrdinary patternOrdinary stage)
      (DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.StatementLayerPrimaryRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects patternOrdinary
          patternRejects stage)
      (DeclarativeGrammar.AssignmentOrExpressionStatementRejects
        expressionOrdinary expressionRejects) primaryOutcome.1
          primaryOutcome.2 fallbackSuccess fallbackReject).1 result)⟩

end Solcore.Syntax.Parser.TermInternals.StatementLayerSuccessInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementLayerOrdinaryRejectionPrimitiveProperties
/-! Primitive bridges used by the ordered Core statement rejection proof. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

abbrev StatementLayerExecutableOutcomeSound {α : Type} (parser : Parser α)
    (ordinary : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop)
    (rejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop) : Prop :=
  (∀ {input output : State} {value : α}, parser input = .ok value output →
    ordinary input.declarativeRemainder value output.declarativeRemainder) ∧
  (∀ {input rejected : State} {failure : Failure},
    parser input = .reject failure rejected →
      rejects input.declarativeRemainder rejected.declarativeRemainder)

theorem statementLayerKeywordTokenAt_of_isKeyword_eq_true
    (value : HardKeyword) {input : State}
    (present : isKeyword input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .statement present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .statement parsed).1⟩

theorem statementLayerContextualTokenAt_of_isContextual_eq_true
    (value : ContextualKeyword) {input : State}
    (present : isContextual input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.identifier value.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true value .statement present
    with ⟨token, parsed⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses value .statement parsed).1⟩

theorem statementLayerSymbolTokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    DeclarativeGrammar.StatementLayerTokenAt input.declarativeRemainder
      (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .statement present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .statement parsed).1⟩

theorem statementLayerSelectedGuarded_reject
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects expressionRejects patternRejects :
      DeclarativeGrammar.Remainder → DeclarativeGrammar.Remainder → Prop}
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    (stage : DeclarativeGrammar.StatementLayerStage)
    (notFallback : stage ≠ .fallback)
    {input rejected : State} {failure : Failure}
    (priority : DeclarativeGrammar.StatementLayerPrefixAbsent
      input.declarativeRemainder stage)
    (guard : DeclarativeGrammar.StatementLayerGuardAt
      input.declarativeRemainder stage)
    (primary fallback : Parser Statement)
    (primarySound : StatementLayerExecutableOutcomeSound primary
      (DeclarativeGrammar.StatementLayerPrimaryOrdinaryParses
        statementOrdinary expressionOrdinary patternOrdinary stage)
      (DeclarativeGrammar.StatementLayerPrimaryRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects patternOrdinary
          patternRejects stage))
    (fallbackSound : StatementLayerExecutableOutcomeSound fallback
      (DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.AssignmentOrExpressionStatementRejects
        expressionOrdinary expressionRejects))
    (result : recognizedStatementOrFallback primary fallback input =
      .reject failure rejected) :
    DeclarativeGrammar.StatementLayerRejects statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  refine ⟨stage, .guarded notFallback priority guard ?_⟩
  exact (recognizedStatementOrFallback_ordinaryOutcome_sound primary fallback
    (DeclarativeGrammar.StatementLayerPrimaryOrdinaryParses
      statementOrdinary expressionOrdinary patternOrdinary stage)
    (DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
      expressionOrdinary)
    (DeclarativeGrammar.StatementLayerPrimaryRejects statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects stage)
    (DeclarativeGrammar.AssignmentOrExpressionStatementRejects
      expressionOrdinary expressionRejects)
    primarySound.1 primarySound.2 fallbackSound.1 fallbackSound.2).2 result

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemSoundnessProperties
/-!
Exact diagnostic-free soundness and strict progress for Core `for` header
items.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components_variant {alpha beta : Type} {first : Parser alpha}
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

namespace StatementSimpleInternals

@[simp] theorem forLetEnd_eq_declarative (name : Identifier)
    (type : Option TypeExpr) (initializer : Option Expr) :
    forLetEnd name type initializer =
      DeclarativeGrammar.forLetEnd name type initializer := by
  rfl

theorem forLetItem_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {item : ForItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forLetItem expression input = .ok item next) :
    DeclarativeGrammar.ForLetItemParses expressionParses
      input.declarativeRemainder item next.declarativeRemainder := by
  unfold forLetItem at result
  rcases bind_ok_components_variant result with
    ⟨marker, afterMarker, markerResult, nameStage⟩
  rcases bind_ok_components_variant nameStage with
    ⟨name, afterName, nameResult, typeStage⟩
  rcases bind_ok_components_variant typeStage with
    ⟨type, afterType, typeResult, initializerStage⟩
  rcases bind_ok_components_variant initializerStage with
    ⟨initializer, afterInitializer, initializerResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .letKw .statement markerResult)
    (identifier_success_sound .statement nameResult)
    (optionalLetType_success_sound typeResult)
    (optionalLetInitializer_success_sound expression expressionParses
      expressionSound diagnosticFree initializerResult)

theorem forAssignmentOrExpression_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {item : ForItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forAssignmentOrExpression expression input = .ok item next) :
    DeclarativeGrammar.ForAssignmentOrExpressionParses expressionParses
      input.declarativeRemainder item next.declarativeRemainder := by
  unfold forAssignmentOrExpression at result
  rcases bind_ok_components_variant result with
    ⟨left, afterLeft, leftResult, tailStage⟩
  rcases bind_ok_components_variant tailStage with
    ⟨tail, afterTail, tailResult, finished⟩
  have afterTailFree : afterTail.diagnosticsRev = [] := by
    cases tail with
    | none => cases finished; exact diagnosticFree
    | some tail =>
        cases tail <;> cases finished <;> exact diagnosticFree
  have afterLeftFree :=
    optionalAssignmentTail_reflectsDiagnosticFreeOnSuccess expression
      expressionReflects afterLeft tail afterTail tailResult afterTailFree
  have leftGrammar := expressionSound afterLeftFree leftResult
  have tailGrammar := optionalAssignmentTail_success_sound expression
    expressionParses expressionSound afterTailFree tailResult
  cases tail with
  | none =>
      cases finished
      exact ⟨left, afterLeft.declarativeRemainder, none, leftGrammar,
        tailGrammar, .expression left⟩
  | some tail =>
      cases tail with
      | value operator right =>
          cases finished
          exact ⟨left, afterLeft.declarativeRemainder,
            some (.value operator right), leftGrammar, tailGrammar,
            .value left right operator⟩
      | bitNot operator =>
          cases finished
          exact ⟨left, afterLeft.declarativeRemainder,
            some (.bitNot operator), leftGrammar, tailGrammar,
            .bitNot left operator⟩

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem forItem_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {item : ForItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forItem expression input = .ok item next) :
    DeclarativeGrammar.ForItemParses expressionParses
      input.declarativeRemainder item next.declarativeRemainder := by
  unfold forItem at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    exact .letItem
      (StatementSimpleInternals.forLetItem_success_sound expression
        expressionParses expressionSound diagnosticFree result)
  · have letAbsent : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letAbsent, Bool.false_eq_true, if_false] at result
    exact .assignmentOrExpression
      (keywordAbsentAt_of_isKeyword_eq_false .letKw letAbsent)
      (StatementSimpleInternals.forAssignmentOrExpression_success_sound
        expression expressionParses expressionReflects expressionSound
          diagnosticFree result)

/-- A successful public item advances whenever the expression parser does. -/
theorem forItem_cursor_lt_onSuccess_of_expressionStrict
    (expression : Parser Expr)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    {input next : State} {item : ForItem}
    (result : forItem expression input = .ok item next) :
    input.cursor < next.cursor := by
  unfold forItem at result
  split at result
  · exact StatementSimpleInternals.forLetItem_cursor_lt_onSuccess
      expression (fun _ _ _ parsed => Nat.le_of_lt (expressionStrict parsed))
        result
  · exact
      StatementSimpleInternals.forAssignmentOrExpression_cursor_lt_onSuccess
        expression expressionStrict result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemsOrdinarySuccessSoundnessProperties
/-! Executable ordinary success for public Core `for` item lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Every public success is the non-consuming prioritized stop or a forward
list with one progressing first item and its exact tail. -/
theorem forItems_success_ordinary_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    {input output : State} {items : List ForItem}
    (result : forItems expression stop input = .ok items output) :
    DeclarativeGrammar.ForItemsOrdinaryParses expressionOrdinary stop
      input.declarativeRemainder items output.declarativeRemainder := by
  unfold forItems at result
  cases stopPresent : isSymbol input stop with
  | true =>
      simp only [stopPresent, if_true] at result
      cases result
      rcases symbolTokenAt_of_isSymbol_eq_true stop stopPresent with
        ⟨stopSpan, stopCurrent⟩
      exact .empty stopSpan stopCurrent
  | false =>
      simp only [stopPresent, Bool.false_eq_true, if_false] at result
      cases itemResult : forItem expression input with
      | invariant error => simp [itemResult] at result
      | reject failure rejected => simp [itemResult] at result
      | ok first afterFirst =>
          simp only [itemResult] at result
          rcases forItemsTail_success_ordinary_sound expression stop
              expressionOrdinary expressionSuccessSound
              (afterFirst.remainingCount + 1) [first] afterFirst items output
                result with
            ⟨suffix, itemsEq, tailParsed⟩
          have progress := forItem_cursor_lt_onSuccess_of_expressionStrict
            expression expressionStrict itemResult
          rw [itemsEq]
          simpa using DeclarativeGrammar.ForItemsParses.nonempty
            (symbolAbsentAt_of_isSymbol_eq_false stop stopPresent)
            (forItem_success_ordinary_sound expression expressionOrdinary
              expressionSuccessSound itemResult)
            (by simpa [State.declarativeRemainder] using progress)
            tailParsed

end Solcore.Syntax.Parser.ControlInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemsOrdinaryRejectionSoundnessProperties
/-! Executable exact rejection for public Core `for` item lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Every public rejection follows stop absence and then the rejected first
item or a progressing first item followed by exact tail rejection. -/
theorem forItems_reject_ordinary_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    {input rejected : State} {failure : Failure}
    (result : forItems expression stop input = .reject failure rejected) :
    DeclarativeGrammar.ForItemsRejects expressionOrdinary expressionRejects
      stop input.declarativeRemainder rejected.declarativeRemainder := by
  unfold forItems at result
  cases stopPresent : isSymbol input stop with
  | true => simp [stopPresent] at result
  | false =>
      simp only [stopPresent, Bool.false_eq_true, if_false] at result
      have stopAbsent := symbolAbsentAt_of_isSymbol_eq_false stop stopPresent
      cases itemResult : forItem expression input with
      | invariant error => simp [itemResult] at result
      | reject itemFailure itemRejected =>
          simp only [itemResult] at result
          cases result
          exact .firstRejected stopAbsent
            (forItem_reject_ordinary_sound expression expressionOrdinary
              expressionRejects expressionSuccessSound expressionRejectSound
                itemResult)
      | ok first afterFirst =>
          simp only [itemResult] at result
          have progress := forItem_cursor_lt_onSuccess_of_expressionStrict
            expression expressionStrict itemResult
          exact .tailRejected stopAbsent
            (forItem_success_ordinary_sound expression expressionOrdinary
              expressionSuccessSound itemResult)
            (by simpa [State.declarativeRemainder] using progress)
            (forItemsTail_reject_ordinary_sound expression stop
              expressionOrdinary expressionRejects expressionSuccessSound
                expressionRejectSound (afterFirst.remainingCount + 1)
                  [first] afterFirst failure rejected result)

end Solcore.Syntax.Parser.ControlInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemsOrdinaryOutcomeSoundnessProperties
/-! Packaged executable ordinary outcomes for public Core `for` item lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Package executable success and exact rejection for public item lists. -/
theorem forItems_ordinaryOutcome_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor) :
    (∀ {input output : State} {items : List ForItem},
      forItems expression stop input = .ok items output →
        DeclarativeGrammar.ForItemsOrdinaryParses expressionOrdinary stop
          input.declarativeRemainder items output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forItems expression stop input = .reject failure rejected →
        DeclarativeGrammar.ForItemsRejects expressionOrdinary
          expressionRejects stop input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨forItems_success_ordinary_sound expression stop expressionOrdinary
      expressionSuccessSound expressionStrict,
    forItems_reject_ordinary_sound expression stop expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound
        expressionStrict⟩

/-- Re-export deterministic public Core `for` item-list outcomes. -/
theorem forItems_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) (stop : Symbol) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForItemsOrdinaryParses expressionOrdinary stop)
      (DeclarativeGrammar.ForItemsRejects expressionOrdinary expressionRejects
        stop) :=
  DeclarativeGrammar.forItemsDeterministicOutcomeSpec expressionOutcomes stop

end Solcore.Syntax.Parser.ControlInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForStatementOrdinarySuccessSoundnessProperties
/-! Executable ordinary success for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable Core `for` success retains its exact header, recursive
body, AST spans, item order, and final remainder. -/
theorem forStatement_success_ordinary_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    {input output : State} {value : Statement}
    (result : forStatement statement expression input = .ok value output) :
    DeclarativeGrammar.ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold forStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, openingStage⟩
  rcases bind_ok_components openingStage with
    ⟨opening, afterOpening, openingResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult,
      firstSemicolonStage⟩
  rcases bind_ok_components firstSemicolonStage with
    ⟨firstSemicolon, afterFirstSemicolon, firstSemicolonResult,
      conditionStage⟩
  rcases bind_ok_components conditionStage with
    ⟨condition, afterCondition, conditionResult, secondSemicolonStage⟩
  rcases bind_ok_components secondSemicolonStage with
    ⟨secondSemicolon, afterSecondSemicolon, secondSemicolonResult,
      postStage⟩
  rcases bind_ok_components postStage with
    ⟨post, afterPost, postResult, closingStage⟩
  rcases bind_ok_components closingStage with
    ⟨closing, afterClosing, closingResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span opening.span firstSemicolon.span
    secondSemicolon.span closing.span
    (keyword_success_exactTokenParses .forKw .statement markerResult)
    (symbol_success_exactTokenParses .leftParen .statement openingResult)
    (ControlInternals.forItems_success_ordinary_sound expression .semicolon
      expressionOrdinary expressionSuccessSound expressionStrict
        initializerResult)
    (symbol_success_exactTokenParses .semicolon .statement
      firstSemicolonResult)
    (expressionSuccessSound conditionResult)
    (symbol_success_exactTokenParses .semicolon .statement
      secondSemicolonResult)
    (ControlInternals.forItems_success_ordinary_sound expression .rightParen
      expressionOrdinary expressionSuccessSound expressionStrict postResult)
    (symbol_success_exactTokenParses .rightParen .statement closingResult)
    ((coreBlock_ordinaryOutcome_sound statement .require statementOrdinary
      statementRejects statementSuccessSound statementRejectSound).1
        bodyResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForStatementOrdinaryRejectionSoundnessProperties
/-! Executable exact rejection for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable Core `for` rejection records its first rejected stage. -/
theorem forStatement_reject_ordinary_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    {input rejected : State} {failure : Failure}
    (result : forStatement statement expression input =
      .reject failure rejected) :
    DeclarativeGrammar.ForStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold forStatement at result
  cases markerResult : keyword .forKw .statement input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .forKw .statement
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .forKw .statement markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .forKw .statement
        markerResult
      cases openingResult : symbol .leftParen .statement afterMarker with
      | invariant error => simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have rejectedEq := symbol_reject_state_eq .leftParen .statement
            openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          exact .openingMissing marker.span markerParsed
            (symbol_reject_tokenKindAbsentAt .leftParen .statement
              openingResult)
      | ok opening afterOpening =>
          simp only [openingResult] at result
          have openingParsed := symbol_success_exactTokenParses .leftParen
            .statement openingResult
          cases initializerResult : ControlInternals.forItems expression
              .semicolon afterOpening with
          | invariant error => simp [initializerResult] at result
          | reject initializerFailure initializerRejected =>
              simp only [initializerResult] at result
              cases result
              exact .initializerRejected marker.span opening.span markerParsed
                openingParsed
                (ControlInternals.forItems_reject_ordinary_sound expression
                  .semicolon expressionOrdinary expressionRejects
                    expressionSuccessSound expressionRejectSound
                      expressionStrict initializerResult)
          | ok initializer afterInitializer =>
              simp only [initializerResult] at result
              have initializerParsed :=
                ControlInternals.forItems_success_ordinary_sound expression
                  .semicolon expressionOrdinary expressionSuccessSound
                    expressionStrict initializerResult
              cases firstSemicolonResult : symbol .semicolon .statement
                  afterInitializer with
              | invariant error => simp [firstSemicolonResult] at result
              | reject semicolonFailure semicolonRejected =>
                  have rejectedEq := symbol_reject_state_eq .semicolon
                    .statement firstSemicolonResult
                  subst semicolonRejected
                  simp only [firstSemicolonResult] at result
                  cases result
                  exact .firstSemicolonMissing marker.span opening.span
                    markerParsed openingParsed initializerParsed
                    (symbol_reject_tokenKindAbsentAt .semicolon .statement
                      firstSemicolonResult)
              | ok firstSemicolon afterFirstSemicolon =>
                  simp only [firstSemicolonResult] at result
                  have firstSemicolonParsed :=
                    symbol_success_exactTokenParses .semicolon .statement
                      firstSemicolonResult
                  cases conditionResult : expression afterFirstSemicolon with
                  | invariant error => simp [conditionResult] at result
                  | reject conditionFailure conditionRejected =>
                      simp only [conditionResult] at result
                      cases result
                      exact .conditionRejected marker.span opening.span
                        firstSemicolon.span markerParsed openingParsed
                        initializerParsed firstSemicolonParsed
                        (expressionRejectSound conditionResult)
                  | ok condition afterCondition =>
                      simp only [conditionResult] at result
                      have conditionParsed := expressionSuccessSound
                        conditionResult
                      cases secondSemicolonResult :
                          symbol .semicolon .statement afterCondition with
                      | invariant error =>
                          simp [secondSemicolonResult] at result
                      | reject semicolonFailure semicolonRejected =>
                          have rejectedEq := symbol_reject_state_eq .semicolon
                            .statement secondSemicolonResult
                          subst semicolonRejected
                          simp only [secondSemicolonResult] at result
                          cases result
                          exact .secondSemicolonMissing marker.span
                            opening.span firstSemicolon.span markerParsed
                            openingParsed initializerParsed
                            firstSemicolonParsed conditionParsed
                            (symbol_reject_tokenKindAbsentAt .semicolon
                              .statement secondSemicolonResult)
                      | ok secondSemicolon afterSecondSemicolon =>
                          simp only [secondSemicolonResult] at result
                          have secondSemicolonParsed :=
                            symbol_success_exactTokenParses .semicolon
                              .statement secondSemicolonResult
                          cases postResult : ControlInternals.forItems
                              expression .rightParen afterSecondSemicolon with
                          | invariant error => simp [postResult] at result
                          | reject postFailure postRejected =>
                              simp only [postResult] at result
                              cases result
                              exact .postRejected marker.span opening.span
                                firstSemicolon.span secondSemicolon.span
                                markerParsed openingParsed initializerParsed
                                firstSemicolonParsed conditionParsed
                                secondSemicolonParsed
                                (ControlInternals.forItems_reject_ordinary_sound
                                  expression .rightParen expressionOrdinary
                                  expressionRejects expressionSuccessSound
                                  expressionRejectSound expressionStrict
                                  postResult)
                          | ok post afterPost =>
                              simp only [postResult] at result
                              have postParsed :=
                                ControlInternals.forItems_success_ordinary_sound
                                  expression .rightParen expressionOrdinary
                                  expressionSuccessSound expressionStrict
                                  postResult
                              cases closingResult : symbol .rightParen
                                  .statement afterPost with
                              | invariant error =>
                                  simp [closingResult] at result
                              | reject closingFailure closingRejected =>
                                  have rejectedEq := symbol_reject_state_eq
                                    .rightParen .statement closingResult
                                  subst closingRejected
                                  simp only [closingResult] at result
                                  cases result
                                  exact .closingMissing marker.span
                                    opening.span firstSemicolon.span
                                    secondSemicolon.span markerParsed
                                    openingParsed initializerParsed
                                    firstSemicolonParsed conditionParsed
                                    secondSemicolonParsed postParsed
                                    (symbol_reject_tokenKindAbsentAt
                                      .rightParen .statement closingResult)
                              | ok closing afterClosing =>
                                  simp only [closingResult] at result
                                  have closingParsed :=
                                    symbol_success_exactTokenParses
                                      .rightParen .statement closingResult
                                  cases bodyResult : coreBlock statement
                                      .require afterClosing with
                                  | invariant error =>
                                      simp [bodyResult] at result
                                  | ok body output =>
                                      simp [bodyResult, pure] at result
                                  | reject bodyFailure bodyRejected =>
                                      simp only [bodyResult] at result
                                      cases result
                                      exact .bodyRejected marker.span
                                        opening.span firstSemicolon.span
                                        secondSemicolon.span closing.span
                                        markerParsed openingParsed
                                        initializerParsed firstSemicolonParsed
                                        conditionParsed secondSemicolonParsed
                                        postParsed closingParsed
                                        ((coreBlock_ordinaryOutcome_sound
                                          statement .require
                                          statementOrdinary statementRejects
                                          statementSuccessSound
                                          statementRejectSound).2 bodyResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForStatementOrdinaryOutcomeSoundnessProperties
/-! Packaged executable ordinary outcomes for complete Core `for`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable success and exact rejection for Core `for`. -/
theorem forStatement_ordinaryOutcome_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor) :
    (∀ {input output : State} {value : Statement},
      forStatement statement expression input = .ok value output →
        DeclarativeGrammar.ForStatementOrdinaryParses statementOrdinary
          expressionOrdinary input.declarativeRemainder value
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forStatement statement expression input = .reject failure rejected →
        DeclarativeGrammar.ForStatementRejects statementOrdinary
          statementRejects expressionOrdinary expressionRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨forStatement_success_ordinary_sound statement expression
      statementOrdinary statementRejects expressionOrdinary
        statementSuccessSound statementRejectSound expressionSuccessSound
          expressionStrict,
    forStatement_reject_ordinary_sound statement expression
      statementOrdinary statementRejects expressionRejects expressionOrdinary
        statementSuccessSound statementRejectSound expressionSuccessSound
          expressionRejectSound expressionStrict⟩

/-- Re-export deterministic Core `for` outcomes. -/
theorem forStatement_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects)
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForStatementOrdinaryParses statementOrdinary
        expressionOrdinary)
      (DeclarativeGrammar.ForStatementRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects) :=
  DeclarativeGrammar.forStatementDeterministicOutcomeSpec statementOutcomes
    expressionOutcomes

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementLayerOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection for the ordered Core statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Every executable statement-layer rejection retains the exact selected
guard, its priority prefix, and the transactional fallback rejection. -/
theorem statementLayer_reject_ordinary_sound
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects expressionRejects patternRejects :
      DeclarativeGrammar.Remainder → DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      nestedStatement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      nestedStatement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : statementLayer nestedStatement expression pattern input =
      .reject failure rejected) :
    DeclarativeGrammar.StatementLayerRejects statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder
          rejected.declarativeRemainder := by
  let fallback := assignmentOrExpressionStatement expression
  have fallbackSound : StatementLayerExecutableOutcomeSound fallback
      (DeclarativeGrammar.AssignmentOrExpressionStatementOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.AssignmentOrExpressionStatementRejects
        expressionOrdinary expressionRejects) :=
    ⟨assignmentOrExpressionStatement_success_ordinary_sound expression
        expressionOrdinary expressionSuccessSound,
      assignmentOrExpressionStatement_reject_ordinary_sound expression
        expressionOrdinary expressionRejects expressionSuccessSound
          expressionRejectSound⟩
  unfold statementLayer at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    exact statementLayerSelectedGuarded_reject .letGuard (by simp) .start
      (statementLayerKeywordTokenAt_of_isKeyword_eq_true .letKw letPresent)
      (letStatement expression) fallback
      (letStatement_ordinaryOutcome_sound expression expressionOrdinary
        expressionRejects expressionSuccessSound expressionRejectSound)
      fallbackSound result
  · have letFalse := Bool.eq_false_iff.mpr letPresent
    simp only [letFalse, Bool.false_eq_true, if_false] at result
    have beforeReturn : DeclarativeGrammar.StatementLayerPrefixAbsent
        input.declarativeRemainder .returnGuard :=
      .afterLet .start (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
    by_cases returnPresent : isKeyword input .returnKw
    · simp only [returnPresent, if_true] at result
      exact statementLayerSelectedGuarded_reject .returnGuard (by simp)
        beforeReturn
        (statementLayerKeywordTokenAt_of_isKeyword_eq_true .returnKw
          returnPresent)
        (returnStatement expression) fallback
        (returnStatement_ordinaryOutcome_sound expression expressionOrdinary
          expressionRejects expressionSuccessSound expressionRejectSound)
        fallbackSound result
    · have returnFalse := Bool.eq_false_iff.mpr returnPresent
      simp only [returnFalse, Bool.false_eq_true, if_false] at result
      have beforeMatch : DeclarativeGrammar.StatementLayerPrefixAbsent
          input.declarativeRemainder .matchGuard := .afterReturn beforeReturn
        (keywordAbsentAt_of_isKeyword_eq_false .returnKw returnFalse)
      by_cases matchPresent : isKeyword input .matchKw
      · simp only [matchPresent, if_true] at result
        exact statementLayerSelectedGuarded_reject .matchGuard (by simp)
          beforeMatch
          (statementLayerKeywordTokenAt_of_isKeyword_eq_true .matchKw
            matchPresent)
          (matchStatement nestedStatement expression pattern) fallback
          (matchStatement_ordinaryOutcome_sound nestedStatement expression
            pattern statementOrdinary statementRejects expressionOrdinary
            expressionRejects patternOrdinary patternRejects
            statementSuccessSound statementRejectSound expressionSuccessSound
            expressionRejectSound expressionWindow patternSuccessSound
            patternRejectSound) fallbackSound result
      · have matchFalse := Bool.eq_false_iff.mpr matchPresent
        simp only [matchFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.StatementLayerPrefixAbsent
            input.declarativeRemainder .forGuard := .afterMatch beforeMatch
          (keywordAbsentAt_of_isKeyword_eq_false .matchKw matchFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          exact statementLayerSelectedGuarded_reject .forGuard (by simp)
            beforeFor
            (statementLayerKeywordTokenAt_of_isKeyword_eq_true .forKw
              forPresent)
            (forStatement nestedStatement expression) fallback
            (forStatement_ordinaryOutcome_sound nestedStatement expression
              statementOrdinary statementRejects expressionRejects
              expressionOrdinary statementSuccessSound statementRejectSound
              expressionSuccessSound expressionRejectSound expressionStrict)
            fallbackSound result
        · have forFalse := Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeWhile : DeclarativeGrammar.StatementLayerPrefixAbsent
              input.declarativeRemainder .whileGuard := .afterFor beforeFor
            (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases whilePresent : isContextual input .while
          · simp only [whilePresent, if_true] at result
            exact statementLayerSelectedGuarded_reject .whileGuard (by simp)
              beforeWhile
              (statementLayerContextualTokenAt_of_isContextual_eq_true .while
                whilePresent)
              (whileStatement nestedStatement expression) fallback
              (whileStatement_ordinaryOutcome_sound nestedStatement expression
                statementOrdinary statementRejects expressionRejects
                expressionOrdinary statementSuccessSound statementRejectSound
                expressionSuccessSound expressionRejectSound)
              fallbackSound result
          · have whileFalse := Bool.eq_false_iff.mpr whilePresent
            simp only [whileFalse, Bool.false_eq_true, if_false] at result
            have beforeIf : DeclarativeGrammar.StatementLayerPrefixAbsent
                input.declarativeRemainder .ifGuard := .afterWhile beforeWhile
              (contextualAbsentAt_of_isContextual_eq_false .while whileFalse)
            by_cases ifPresent : isKeyword input .ifKw
            · simp only [ifPresent, if_true] at result
              exact statementLayerSelectedGuarded_reject .ifGuard (by simp)
                beforeIf
                (statementLayerKeywordTokenAt_of_isKeyword_eq_true .ifKw
                  ifPresent)
                (ifStatement nestedStatement expression) fallback
                (ifStatement_ordinaryOutcome_sound nestedStatement expression
                  statementOrdinary statementRejects expressionRejects
                  expressionOrdinary statementSuccessSound statementRejectSound
                  expressionSuccessSound expressionRejectSound)
                fallbackSound result
            · have ifFalse := Bool.eq_false_iff.mpr ifPresent
              simp only [ifFalse, Bool.false_eq_true, if_false] at result
              have beforeAssembly :
                  DeclarativeGrammar.StatementLayerPrefixAbsent
                    input.declarativeRemainder .assemblyGuard :=
                .afterIf beforeIf
                  (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
              by_cases assemblyPresent : isKeyword input .assemblyKw
              · simp only [assemblyPresent, if_true] at result
                exact statementLayerSelectedGuarded_reject .assemblyGuard
                  (by simp) beforeAssembly
                  (statementLayerKeywordTokenAt_of_isKeyword_eq_true
                    .assemblyKw assemblyPresent)
                  assemblyStatement fallback
                  assemblyStatement_ordinaryOutcome_sound fallbackSound result
              · have assemblyFalse := Bool.eq_false_iff.mpr assemblyPresent
                simp only [assemblyFalse, Bool.false_eq_true, if_false]
                  at result
                have beforeBlock :
                    DeclarativeGrammar.StatementLayerPrefixAbsent
                      input.declarativeRemainder .blockGuard :=
                  .afterAssembly beforeAssembly
                    (keywordAbsentAt_of_isKeyword_eq_false .assemblyKw
                      assemblyFalse)
                by_cases blockPresent : isSymbol input .leftBrace
                · simp only [blockPresent, if_true] at result
                  exact statementLayerSelectedGuarded_reject .blockGuard
                    (by simp) beforeBlock
                    (statementLayerSymbolTokenAt_of_isSymbol_eq_true .leftBrace
                      blockPresent)
                    (blockStatement nestedStatement) fallback
                    (blockStatement_ordinaryOutcome_sound nestedStatement
                      statementOrdinary statementRejects statementSuccessSound
                      statementRejectSound) fallbackSound result
                · have blockFalse := Bool.eq_false_iff.mpr blockPresent
                  simp only [blockFalse, Bool.false_eq_true, if_false] at result
                  have beforeBreak :
                      DeclarativeGrammar.StatementLayerPrefixAbsent
                        input.declarativeRemainder .breakGuard :=
                    .afterBlock beforeBlock
                      (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
                  by_cases breakPresent : isKeyword input .breakKw
                  · simp only [breakPresent, if_true] at result
                    exact statementLayerSelectedGuarded_reject .breakGuard
                      (by simp) beforeBreak
                      (statementLayerKeywordTokenAt_of_isKeyword_eq_true
                        .breakKw breakPresent)
                      breakStatement fallback
                      (ControlInternals.terminatedControl_ordinaryOutcome_sound .breakKw
                        .breakStmt) fallbackSound result
                  · have breakFalse := Bool.eq_false_iff.mpr breakPresent
                    simp only [breakFalse, Bool.false_eq_true, if_false]
                      at result
                    have beforeContinue :
                        DeclarativeGrammar.StatementLayerPrefixAbsent
                          input.declarativeRemainder .continueGuard :=
                      .afterBreak beforeBreak
                        (keywordAbsentAt_of_isKeyword_eq_false .breakKw
                          breakFalse)
                    by_cases continuePresent : isKeyword input .continueKw
                    · simp only [continuePresent, if_true] at result
                      exact statementLayerSelectedGuarded_reject .continueGuard
                        (by simp) beforeContinue
                        (statementLayerKeywordTokenAt_of_isKeyword_eq_true
                          .continueKw continuePresent)
                        continueStatement fallback
                        (ControlInternals.terminatedControl_ordinaryOutcome_sound .continueKw
                          .continueStmt) fallbackSound result
                    · have continueFalse :=
                        Bool.eq_false_iff.mpr continuePresent
                      simp only [continueFalse, Bool.false_eq_true, if_false]
                        at result
                      have beforeFallback :
                          DeclarativeGrammar.StatementLayerPrefixAbsent
                            input.declarativeRemainder .fallback :=
                        .afterContinue beforeContinue
                          (keywordAbsentAt_of_isKeyword_eq_false .continueKw
                            continueFalse)
                      exact ⟨.fallback, .fallback beforeFallback
                        (fallbackSound.2 result)⟩

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementLayerOrdinarySuccessSoundnessProperties
/-! Ordinary-success reflection for the ordered Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

open StatementLayerSuccessInternals

/-- Every executable statement-layer success selects its exact prioritized
ordinary branch, including transactional fallback after a primary rejection. -/
theorem statementLayer_success_ordinary_sound
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      nestedStatement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      nestedStatement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input output : State} {value : Statement}
    (result : statementLayer nestedStatement expression pattern input =
      .ok value output) :
    DeclarativeGrammar.StatementLayerOrdinaryParses statementOrdinary
      statementRejects expressionOrdinary expressionRejects patternOrdinary
        patternRejects input.declarativeRemainder value
          output.declarativeRemainder := by
  unfold statementLayer at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    exact selected_guarded_success expression expressionSuccessSound
      expressionRejectSound .letGuard (by simp) .start
        (keyword_guard_of_true .letKw letPresent) (letStatement expression)
          (letStatement_ordinaryOutcome_sound expression expressionOrdinary
            expressionRejects expressionSuccessSound expressionRejectSound)
          result
  · have letFalse : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letFalse, Bool.false_eq_true, if_false] at result
    have beforeReturn : DeclarativeGrammar.StatementLayerPrefixAbsent
        input.declarativeRemainder .returnGuard := .afterLet .start
      (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
    by_cases returnPresent : isKeyword input .returnKw
    · simp only [returnPresent, if_true] at result
      exact selected_guarded_success expression expressionSuccessSound
        expressionRejectSound .returnGuard (by simp) beforeReturn
          (keyword_guard_of_true .returnKw returnPresent)
          (returnStatement expression)
          (returnStatement_ordinaryOutcome_sound expression expressionOrdinary
            expressionRejects expressionSuccessSound expressionRejectSound)
          result
    · have returnFalse : isKeyword input .returnKw = false :=
        Bool.eq_false_iff.mpr returnPresent
      simp only [returnFalse, Bool.false_eq_true, if_false] at result
      have beforeMatch : DeclarativeGrammar.StatementLayerPrefixAbsent
          input.declarativeRemainder .matchGuard := .afterReturn beforeReturn
        (keywordAbsentAt_of_isKeyword_eq_false .returnKw returnFalse)
      by_cases matchPresent : isKeyword input .matchKw
      · simp only [matchPresent, if_true] at result
        exact selected_guarded_success expression expressionSuccessSound
          expressionRejectSound .matchGuard (by simp) beforeMatch
            (keyword_guard_of_true .matchKw matchPresent)
            (matchStatement nestedStatement expression pattern)
            (matchStatement_ordinaryOutcome_sound nestedStatement expression
              pattern statementOrdinary statementRejects expressionOrdinary
                expressionRejects patternOrdinary patternRejects
                  statementSuccessSound statementRejectSound
                    expressionSuccessSound expressionRejectSound
                      expressionWindow patternSuccessSound patternRejectSound)
            result
      · have matchFalse : isKeyword input .matchKw = false :=
          Bool.eq_false_iff.mpr matchPresent
        simp only [matchFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.StatementLayerPrefixAbsent
            input.declarativeRemainder .forGuard := .afterMatch beforeMatch
          (keywordAbsentAt_of_isKeyword_eq_false .matchKw matchFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          exact selected_guarded_success expression expressionSuccessSound
            expressionRejectSound .forGuard (by simp) beforeFor
              (keyword_guard_of_true .forKw forPresent)
              (forStatement nestedStatement expression)
              (forStatement_ordinaryOutcome_sound nestedStatement expression
                statementOrdinary statementRejects expressionRejects
                  expressionOrdinary statementSuccessSound
                    statementRejectSound expressionSuccessSound
                      expressionRejectSound expressionStrict) result
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeWhile : DeclarativeGrammar.StatementLayerPrefixAbsent
              input.declarativeRemainder .whileGuard := .afterFor beforeFor
            (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases whilePresent : isContextual input .while
          · simp only [whilePresent, if_true] at result
            exact selected_guarded_success expression expressionSuccessSound
              expressionRejectSound .whileGuard (by simp) beforeWhile
                (contextual_guard_of_true .while whilePresent)
                (whileStatement nestedStatement expression)
                (whileStatement_ordinaryOutcome_sound nestedStatement
                  expression statementOrdinary statementRejects
                    expressionRejects expressionOrdinary statementSuccessSound
                      statementRejectSound expressionSuccessSound
                        expressionRejectSound) result
          · have whileFalse : isContextual input .while = false :=
              Bool.eq_false_iff.mpr whilePresent
            simp only [whileFalse, Bool.false_eq_true, if_false] at result
            have beforeIf : DeclarativeGrammar.StatementLayerPrefixAbsent
                input.declarativeRemainder .ifGuard := .afterWhile beforeWhile
              (contextualAbsentAt_of_isContextual_eq_false .while whileFalse)
            by_cases ifPresent : isKeyword input .ifKw
            · simp only [ifPresent, if_true] at result
              exact selected_guarded_success expression expressionSuccessSound
                expressionRejectSound .ifGuard (by simp) beforeIf
                  (keyword_guard_of_true .ifKw ifPresent)
                  (ifStatement nestedStatement expression)
                  (ifStatement_ordinaryOutcome_sound nestedStatement expression
                    statementOrdinary statementRejects expressionRejects
                      expressionOrdinary statementSuccessSound
                        statementRejectSound expressionSuccessSound
                          expressionRejectSound) result
            · have ifFalse : isKeyword input .ifKw = false :=
                Bool.eq_false_iff.mpr ifPresent
              simp only [ifFalse, Bool.false_eq_true, if_false] at result
              have beforeAssembly : DeclarativeGrammar.StatementLayerPrefixAbsent
                  input.declarativeRemainder .assemblyGuard := .afterIf beforeIf
                (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
              by_cases assemblyPresent : isKeyword input .assemblyKw
              · simp only [assemblyPresent, if_true] at result
                exact selected_guarded_success expression expressionSuccessSound
                  expressionRejectSound .assemblyGuard (by simp) beforeAssembly
                    (keyword_guard_of_true .assemblyKw assemblyPresent)
                    assemblyStatement assemblyStatement_ordinaryOutcome_sound
                    result
              · have assemblyFalse : isKeyword input .assemblyKw = false :=
                  Bool.eq_false_iff.mpr assemblyPresent
                simp only [assemblyFalse, Bool.false_eq_true, if_false]
                  at result
                have beforeBlock : DeclarativeGrammar.StatementLayerPrefixAbsent
                    input.declarativeRemainder .blockGuard :=
                  .afterAssembly beforeAssembly
                    (keywordAbsentAt_of_isKeyword_eq_false .assemblyKw
                      assemblyFalse)
                by_cases blockPresent : isSymbol input .leftBrace
                · simp only [blockPresent, if_true] at result
                  exact selected_guarded_success expression
                    expressionSuccessSound expressionRejectSound .blockGuard
                      (by simp) beforeBlock
                        (symbol_guard_of_true .leftBrace blockPresent)
                        (blockStatement nestedStatement)
                        (blockStatement_ordinaryOutcome_sound nestedStatement
                          statementOrdinary statementRejects
                            statementSuccessSound statementRejectSound) result
                · have blockFalse : isSymbol input .leftBrace = false :=
                    Bool.eq_false_iff.mpr blockPresent
                  simp only [blockFalse, Bool.false_eq_true, if_false] at result
                  have beforeBreak :
                      DeclarativeGrammar.StatementLayerPrefixAbsent
                        input.declarativeRemainder .breakGuard :=
                    .afterBlock beforeBlock
                      (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
                  by_cases breakPresent : isKeyword input .breakKw
                  · simp only [breakPresent, if_true] at result
                    exact selected_guarded_success expression
                      expressionSuccessSound expressionRejectSound .breakGuard
                        (by simp) beforeBreak
                          (keyword_guard_of_true .breakKw breakPresent)
                          breakStatement
                          (ControlInternals.terminatedControl_ordinaryOutcome_sound
                            .breakKw .breakStmt) result
                  · have breakFalse : isKeyword input .breakKw = false :=
                      Bool.eq_false_iff.mpr breakPresent
                    simp only [breakFalse, Bool.false_eq_true, if_false]
                      at result
                    have beforeContinue :
                        DeclarativeGrammar.StatementLayerPrefixAbsent
                          input.declarativeRemainder .continueGuard :=
                      .afterBreak beforeBreak
                        (keywordAbsentAt_of_isKeyword_eq_false .breakKw
                          breakFalse)
                    by_cases continuePresent : isKeyword input .continueKw
                    · simp only [continuePresent, if_true] at result
                      exact selected_guarded_success expression
                        expressionSuccessSound expressionRejectSound
                          .continueGuard (by simp) beforeContinue
                            (keyword_guard_of_true .continueKw continuePresent)
                            continueStatement
                            (ControlInternals.terminatedControl_ordinaryOutcome_sound
                              .continueKw .continueStmt) result
                    · have continueFalse :
                          isKeyword input .continueKw = false :=
                        Bool.eq_false_iff.mpr continuePresent
                      simp only [continueFalse, Bool.false_eq_true, if_false]
                        at result
                      have beforeFallback :
                          DeclarativeGrammar.StatementLayerPrefixAbsent
                            input.declarativeRemainder .fallback :=
                        .afterContinue beforeContinue
                          (keywordAbsentAt_of_isKeyword_eq_false .continueKw
                            continueFalse)
                      exact ⟨.fallback, .fallback beforeFallback
                        (assignmentOrExpressionStatement_success_ordinary_sound
                          expression expressionOrdinary expressionSuccessSound
                            result)⟩

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementLayerOrdinaryOutcomeSoundnessProperties
/-! Packaged ordinary outcomes for the ordered Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Package executable success and exact rejection for one Core statement
layer with the same recursive callbacks. -/
theorem statementLayer_ordinaryOutcome_sound
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      nestedStatement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      nestedStatement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {value : Statement},
      statementLayer nestedStatement expression pattern input =
          .ok value output →
        DeclarativeGrammar.StatementLayerOrdinaryParses statementOrdinary
          statementRejects expressionOrdinary expressionRejects
            patternOrdinary patternRejects input.declarativeRemainder value
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      statementLayer nestedStatement expression pattern input =
          .reject failure rejected →
        DeclarativeGrammar.StatementLayerRejects statementOrdinary
          statementRejects expressionOrdinary expressionRejects
            patternOrdinary patternRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨statementLayer_success_ordinary_sound nestedStatement expression pattern
      statementOrdinary statementRejects expressionOrdinary expressionRejects
        patternOrdinary patternRejects statementSuccessSound
          statementRejectSound expressionSuccessSound expressionRejectSound
            expressionWindow expressionStrict patternSuccessSound
              patternRejectSound,
    statementLayer_reject_ordinary_sound nestedStatement expression pattern
      statementOrdinary statementRejects expressionRejects patternRejects
        expressionOrdinary patternOrdinary statementSuccessSound
          statementRejectSound expressionSuccessSound expressionRejectSound
            expressionWindow expressionStrict patternSuccessSound
              patternRejectSound⟩

/-- Re-export the deterministic contract under the executable bridge name. -/
theorem statementLayer_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects)
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (patternOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      patternOrdinary patternRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.StatementLayerOrdinaryParses statementOrdinary
        statementRejects expressionOrdinary expressionRejects patternOrdinary
          patternRejects)
      (DeclarativeGrammar.StatementLayerRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects patternOrdinary
          patternRejects) :=
  DeclarativeGrammar.statementLayerDeterministicOutcomeSpec statementOutcomes
    expressionOutcomes patternOutcomes

end Solcore.Syntax.Parser.TermInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForItemsSoundnessProperties
/-!
Exact diagnostic-free soundness for the reverse-accumulating Core `for` item
loop and its public forward-order list parser.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

private theorem symbolTokenAt_of_isSymbol_eq_true_variant (symbolValue : Symbol)
    {input : State} (present : isSymbol input symbolValue = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol symbolValue } := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol symbolValue) = true at present
      have parsed : symbol symbolValue .statement input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold symbol acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span, (symbol_ok_tokenAt symbolValue .statement parsed).1⟩

/--
The executable reverse accumulator is the prefix of the returned list; the
declarative tail is the remaining forward suffix.
-/
theorem forItemsTail_success_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder) :
    ∀ fuel itemsRev input items next,
      next.diagnosticsRev = [] →
      forItemsTail expression stop fuel itemsRev input = .ok items next →
      ∃ suffix,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.ForItemsTailParses expressionParses stop
          input.declarativeRemainder suffix next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items next diagnosticFree result
      simp [forItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input items next diagnosticFree result
      unfold forItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp only [commaPresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (symbolAbsentAt_of_isSymbol_eq_false .comma commaPresent),
            diagnosticFree⟩
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .statement input with
          | invariant error => simp [commaResult] at result
          | reject failure rejected => simp [commaResult] at result
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases stopPresent : isSymbol afterComma stop with
              | true =>
                  simp only [stopPresent, if_true] at result
                  unfold rejectAt at result
                  contradiction
              | false =>
                  simp only [stopPresent, Bool.false_eq_true, if_false] at result
                  cases itemResult : forItem expression afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject failure rejected => simp [itemResult] at result
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      by_cases progress : afterItem.cursor > afterComma.cursor
                      · simp only [progress, if_true] at result
                        rcases inductionHypothesis (item :: itemsRev)
                            afterItem items next diagnosticFree result with
                          ⟨suffix, itemsEq, tailGrammar, afterItemFree⟩
                        have itemGrammar := forItem_success_sound expression
                          expressionParses expressionReflects expressionSound
                            afterItemFree itemResult
                        have afterCommaFree :=
                          forItem_reflectsDiagnosticFreeOnSuccess expression
                            expressionReflects afterComma item afterItem
                              itemResult afterItemFree
                        have inputFree :=
                          symbol_reflectsDiagnosticFreeOnSuccess .comma
                            .statement input comma afterComma commaResult
                              afterCommaFree
                        refine ⟨item :: suffix, ?_,
                          .next comma.span
                            (symbol_success_exactTokenParses .comma .statement
                              commaResult)
                            (symbolAbsentAt_of_isSymbol_eq_false stop
                              stopPresent)
                            itemGrammar (by
                              simpa [State.declarativeRemainder] using
                                progress) tailGrammar,
                          inputFree⟩
                        simpa [List.reverse_cons, List.append_assoc] using
                          itemsEq
                      · simp only [progress, if_false] at result
                        contradiction

/-- Every public success is a forward list with the exact prioritized stop. -/
theorem forItems_success_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    {input next : State} {items : List ForItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forItems expression stop input = .ok items next) :
    DeclarativeGrammar.ForItemsParses expressionParses stop
      input.declarativeRemainder items next.declarativeRemainder := by
  unfold forItems at result
  cases stopPresent : isSymbol input stop with
  | true =>
      simp only [stopPresent, if_true] at result
      cases result
      rcases symbolTokenAt_of_isSymbol_eq_true_variant stop stopPresent with
        ⟨span, stopCurrent⟩
      exact .empty span stopCurrent
  | false =>
      simp only [stopPresent, Bool.false_eq_true, if_false] at result
      cases itemResult : forItem expression input with
      | invariant error => simp [itemResult] at result
      | reject failure rejected => simp [itemResult] at result
      | ok first afterFirst =>
          simp only [itemResult] at result
          rcases forItemsTail_success_sound expression stop expressionParses
              expressionReflects expressionSound
              (afterFirst.remainingCount + 1) [first] afterFirst items next
              diagnosticFree result with
            ⟨suffix, itemsEq, tailGrammar, afterFirstFree⟩
          have firstGrammar := forItem_success_sound expression
            expressionParses expressionReflects expressionSound
              afterFirstFree itemResult
          have progress := forItem_cursor_lt_onSuccess_of_expressionStrict
            expression expressionStrict itemResult
          rw [itemsEq]
          simpa using DeclarativeGrammar.ForItemsParses.nonempty
            (symbolAbsentAt_of_isSymbol_eq_false stop stopPresent)
            firstGrammar (by
              simpa [State.declarativeRemainder] using progress) tailGrammar

end Solcore.Syntax.Parser.ControlInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreForStatementSoundnessProperties
/-!
Exact diagnostic-free soundness for complete canonical Core `for`
statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem forStatement_success_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forStatement statement expression input = .ok value next) :
    DeclarativeGrammar.ForStatementParses statementParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold forStatement at result
  rcases bind_ok_components_variant result with
    ⟨marker, afterMarker, markerResult, openingStage⟩
  rcases bind_ok_components_variant openingStage with
    ⟨opening, afterOpening, openingResult, initializerStage⟩
  rcases bind_ok_components_variant initializerStage with
    ⟨initializer, afterInitializer, initializerResult,
      firstSemicolonStage⟩
  rcases bind_ok_components_variant firstSemicolonStage with
    ⟨firstSemicolon, afterFirstSemicolon, firstSemicolonResult,
      conditionStage⟩
  rcases bind_ok_components_variant conditionStage with
    ⟨condition, afterCondition, conditionResult, secondSemicolonStage⟩
  rcases bind_ok_components_variant secondSemicolonStage with
    ⟨secondSemicolon, afterSecondSemicolon, secondSemicolonResult,
      postStage⟩
  rcases bind_ok_components_variant postStage with
    ⟨post, afterPost, postResult, closingStage⟩
  rcases bind_ok_components_variant closingStage with
    ⟨closing, afterClosing, closingResult, bodyStage⟩
  rcases bind_ok_components_variant bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterClosingFree := coreBlock_reflectsDiagnosticFreeOnSuccess
    statement .require statementReflects afterClosing body next
      bodyResult diagnosticFree
  have afterPostFree := symbol_reflectsDiagnosticFreeOnSuccess .rightParen
    .statement afterPost closing afterClosing closingResult afterClosingFree
  have afterSecondSemicolonFree :=
    ControlInternals.forItems_reflectsDiagnosticFreeOnSuccess expression
      .rightParen expressionReflects afterSecondSemicolon post afterPost
        postResult afterPostFree
  have afterConditionFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .statement afterCondition secondSemicolon
      afterSecondSemicolon secondSemicolonResult afterSecondSemicolonFree
  have afterFirstSemicolonFree := expressionReflects afterFirstSemicolon
    condition afterCondition conditionResult afterConditionFree
  have afterInitializerFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .statement afterInitializer firstSemicolon
      afterFirstSemicolon firstSemicolonResult afterFirstSemicolonFree
  exact .parsed marker.span opening.span firstSemicolon.span
    secondSemicolon.span closing.span
    (keyword_success_exactTokenParses .forKw .statement markerResult)
    (symbol_success_exactTokenParses .leftParen .statement openingResult)
    (ControlInternals.forItems_success_sound expression .semicolon
      expressionParses expressionReflects expressionSound expressionStrict
        afterInitializerFree initializerResult)
    (symbol_success_exactTokenParses .semicolon .statement
      firstSemicolonResult)
    (expressionSound afterConditionFree conditionResult)
    (symbol_success_exactTokenParses .semicolon .statement
      secondSemicolonResult)
    (ControlInternals.forItems_success_sound expression .rightParen
      expressionParses expressionReflects expressionSound expressionStrict
        afterPostFree postResult)
    (symbol_success_exactTokenParses .rightParen .statement closingResult)
    (coreBlock_success_sound statementParses statement .require
      statementReflects statementSound diagnosticFree bodyResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreStatementLayerSoundnessProperties
/-! Exact diagnostic-free soundness for the Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Every clean statement-layer success follows its exact prioritized branch. -/
theorem statementLayer_success_sound
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (patternParses : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (yulBodyParses : DeclarativeGrammar.Remainder → SourceSpan →
      List YulStmt → DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nestedStatement)
    (nestedSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → nestedStatement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionShape : Parser.PreservesTokenWindow expression)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern)
    (patternSound : ∀ {input next : State} {value : Pattern},
      next.diagnosticsRev = [] → pattern input = .ok value next →
      patternParses input.declarativeRemainder value next.declarativeRemainder)
    (yulBodySound : ∀ {input next : State} {body : YulParsedBlock},
      next.diagnosticsRev = [] → yulBody input = .ok body next →
      yulBodyParses input.declarativeRemainder body.span body.body
        next.declarativeRemainder)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : statementLayer nestedStatement expression pattern input =
      .ok value next) :
    DeclarativeGrammar.StatementLayerParses statementParses expressionParses
      patternParses yulBodyParses input.declarativeRemainder value
        next.declarativeRemainder := by
  unfold statementLayer at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    have primary := recognizedStatementOrFallback_primary_of_diagnosticFree_success
      (letStatement expression) (assignmentOrExpressionStatement expression)
        result diagnosticFree
    exact .letBranch .start (letStatement_success_sound expression
      expressionParses expressionSound diagnosticFree primary)
  · have letFalse : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letFalse, Bool.false_eq_true, if_false] at result
    have beforeReturn : DeclarativeGrammar.StatementLayerPrefixAbsent
        input.declarativeRemainder .returnGuard :=
      .afterLet .start (keywordAbsentAt_of_isKeyword_eq_false .letKw letFalse)
    by_cases returnPresent : isKeyword input .returnKw
    · simp only [returnPresent, if_true] at result
      have primary :=
        recognizedStatementOrFallback_primary_of_diagnosticFree_success
          (returnStatement expression)
            (assignmentOrExpressionStatement expression) result diagnosticFree
      exact .returnBranch beforeReturn (returnStatement_success_sound
        expression expressionParses expressionSound diagnosticFree primary)
    · have returnFalse : isKeyword input .returnKw = false :=
        Bool.eq_false_iff.mpr returnPresent
      simp only [returnFalse, Bool.false_eq_true, if_false] at result
      have beforeMatch : DeclarativeGrammar.StatementLayerPrefixAbsent
          input.declarativeRemainder .matchGuard :=
        .afterReturn beforeReturn
          (keywordAbsentAt_of_isKeyword_eq_false .returnKw returnFalse)
      by_cases matchPresent : isKeyword input .matchKw
      · simp only [matchPresent, if_true] at result
        have primary :=
          recognizedStatementOrFallback_primary_of_diagnosticFree_success
            (matchStatement nestedStatement expression pattern)
              (assignmentOrExpressionStatement expression) result
                diagnosticFree
        exact .matchBranch beforeMatch (matchStatement_success_sound
          nestedStatement expression pattern statementParses expressionParses
            patternParses nestedReflects nestedSound expressionReflects
              expressionSound expressionShape patternReflects patternSound
                diagnosticFree primary)
      · have matchFalse : isKeyword input .matchKw = false :=
          Bool.eq_false_iff.mpr matchPresent
        simp only [matchFalse, Bool.false_eq_true, if_false] at result
        have beforeFor : DeclarativeGrammar.StatementLayerPrefixAbsent
            input.declarativeRemainder .forGuard :=
          .afterMatch beforeMatch
            (keywordAbsentAt_of_isKeyword_eq_false .matchKw matchFalse)
        by_cases forPresent : isKeyword input .forKw
        · simp only [forPresent, if_true] at result
          have primary :=
            recognizedStatementOrFallback_primary_of_diagnosticFree_success
              (forStatement nestedStatement expression)
                (assignmentOrExpressionStatement expression) result
                  diagnosticFree
          exact .forBranch beforeFor (forStatement_success_sound
            nestedStatement expression statementParses expressionParses
              nestedReflects nestedSound expressionReflects expressionSound
                expressionStrict diagnosticFree primary)
        · have forFalse : isKeyword input .forKw = false :=
            Bool.eq_false_iff.mpr forPresent
          simp only [forFalse, Bool.false_eq_true, if_false] at result
          have beforeWhile : DeclarativeGrammar.StatementLayerPrefixAbsent
              input.declarativeRemainder .whileGuard :=
            .afterFor beforeFor
              (keywordAbsentAt_of_isKeyword_eq_false .forKw forFalse)
          by_cases whilePresent : isContextual input .while
          · simp only [whilePresent, if_true] at result
            have primary :=
              recognizedStatementOrFallback_primary_of_diagnosticFree_success
                (whileStatement nestedStatement expression)
                  (assignmentOrExpressionStatement expression) result
                    diagnosticFree
            exact .whileBranch beforeWhile (whileStatement_success_sound
              nestedStatement expression statementParses expressionParses
                nestedReflects nestedSound expressionSound diagnosticFree
                  primary)
          · have whileFalse : isContextual input .while = false :=
              Bool.eq_false_iff.mpr whilePresent
            simp only [whileFalse, Bool.false_eq_true, if_false] at result
            have beforeIf : DeclarativeGrammar.StatementLayerPrefixAbsent
                input.declarativeRemainder .ifGuard :=
              .afterWhile beforeWhile
                (contextualAbsentAt_of_isContextual_eq_false .while whileFalse)
            by_cases ifPresent : isKeyword input .ifKw
            · simp only [ifPresent, if_true] at result
              have primary :=
                recognizedStatementOrFallback_primary_of_diagnosticFree_success
                  (ifStatement nestedStatement expression)
                    (assignmentOrExpressionStatement expression) result
                      diagnosticFree
              exact .ifBranch beforeIf (ifStatement_success_sound
                nestedStatement expression statementParses expressionParses
                  nestedReflects nestedSound expressionSound diagnosticFree
                    primary)
            · have ifFalse : isKeyword input .ifKw = false :=
                Bool.eq_false_iff.mpr ifPresent
              simp only [ifFalse, Bool.false_eq_true, if_false] at result
              have beforeAssembly :
                  DeclarativeGrammar.StatementLayerPrefixAbsent
                    input.declarativeRemainder .assemblyGuard :=
                .afterIf beforeIf
                  (keywordAbsentAt_of_isKeyword_eq_false .ifKw ifFalse)
              by_cases assemblyPresent : isKeyword input .assemblyKw
              · simp only [assemblyPresent, if_true] at result
                have primary :=
                  recognizedStatementOrFallback_primary_of_diagnosticFree_success
                    assemblyStatement (assignmentOrExpressionStatement expression)
                      result diagnosticFree
                exact .assemblyBranch beforeAssembly
                  (assemblyStatement_success_sound yulBodyParses yulBodySound
                    diagnosticFree primary)
              · have assemblyFalse : isKeyword input .assemblyKw = false :=
                  Bool.eq_false_iff.mpr assemblyPresent
                simp only [assemblyFalse, Bool.false_eq_true, if_false] at result
                have beforeBlock :
                    DeclarativeGrammar.StatementLayerPrefixAbsent
                      input.declarativeRemainder .blockGuard :=
                  .afterAssembly beforeAssembly
                    (keywordAbsentAt_of_isKeyword_eq_false .assemblyKw
                      assemblyFalse)
                by_cases blockPresent : isSymbol input .leftBrace
                · simp only [blockPresent, if_true] at result
                  have primary :=
                    recognizedStatementOrFallback_primary_of_diagnosticFree_success
                      (blockStatement nestedStatement)
                        (assignmentOrExpressionStatement expression) result
                          diagnosticFree
                  exact .blockBranch beforeBlock (blockStatement_success_sound
                    nestedStatement statementParses nestedReflects nestedSound
                      diagnosticFree primary)
                · have blockFalse : isSymbol input .leftBrace = false :=
                    Bool.eq_false_iff.mpr blockPresent
                  simp only [blockFalse, Bool.false_eq_true, if_false] at result
                  have beforeBreak :
                      DeclarativeGrammar.StatementLayerPrefixAbsent
                        input.declarativeRemainder .breakGuard :=
                    .afterBlock beforeBlock
                      (symbolAbsentAt_of_isSymbol_eq_false .leftBrace blockFalse)
                  by_cases breakPresent : isKeyword input .breakKw
                  · simp only [breakPresent, if_true] at result
                    have primary :=
                      recognizedStatementOrFallback_primary_of_diagnosticFree_success
                        breakStatement
                          (assignmentOrExpressionStatement expression) result
                            diagnosticFree
                    exact .breakBranch beforeBreak
                      (breakStatement_success_sound primary)
                  · have breakFalse : isKeyword input .breakKw = false :=
                      Bool.eq_false_iff.mpr breakPresent
                    simp only [breakFalse, Bool.false_eq_true, if_false]
                      at result
                    have beforeContinue :
                        DeclarativeGrammar.StatementLayerPrefixAbsent
                          input.declarativeRemainder .continueGuard :=
                      .afterBreak beforeBreak
                        (keywordAbsentAt_of_isKeyword_eq_false .breakKw
                          breakFalse)
                    by_cases continuePresent : isKeyword input .continueKw
                    · simp only [continuePresent, if_true] at result
                      have primary :=
                        recognizedStatementOrFallback_primary_of_diagnosticFree_success
                          continueStatement
                            (assignmentOrExpressionStatement expression) result
                              diagnosticFree
                      exact .continueBranch beforeContinue
                        (continueStatement_success_sound primary)
                    · have continueFalse :
                          isKeyword input .continueKw = false :=
                        Bool.eq_false_iff.mpr continuePresent
                      simp only [continueFalse, Bool.false_eq_true, if_false]
                        at result
                      have beforeFallback :
                          DeclarativeGrammar.StatementLayerPrefixAbsent
                            input.declarativeRemainder .fallback :=
                        .afterContinue beforeContinue
                          (keywordAbsentAt_of_isKeyword_eq_false .continueKw
                            continueFalse)
                      exact .fallbackBranch beforeFallback
                        (assignmentOrExpressionStatement_success_sound
                          expression expressionParses expressionReflects
                            expressionSound diagnosticFree result)

end Solcore.Syntax.Parser.TermInternals
end
