import Solcore.Syntax.Parser.ContractProperties
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-! Parametric diagnostic-free soundness for contract storage fields. -/

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

namespace ContractInternals

/-- Optional initializer parsing reflects diagnostic freedom through its
abstract expression parser. -/
theorem optionalFieldInitializer_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalFieldInitializer expression) := by
  unfold optionalFieldInitializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .equal .contractMember)
    intro equal
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess expressionReflects
    intro value
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- Every diagnostic-free optional initializer success preserves the `=`
priority decision and follows the supplied expression grammar. -/
theorem optionalFieldInitializer_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    {input next : State} {initializer : Option Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalFieldInitializer expression input =
      .ok initializer next) :
    DeclarativeGrammar.OptionalContractFieldInitializerParses
      expressionParses input.declarativeRemainder initializer
        next.declarativeRemainder := by
  unfold optionalFieldInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal
  · simp only [present, if_true] at result
    cases equalResult : symbol .equal .contractMember input with
    | invariant error => simp [equalResult] at result
    | reject failure rejected => simp [equalResult] at result
    | ok equal afterEqual =>
        simp only [equalResult] at result
        cases valueResult : expression afterEqual with
        | invariant error => simp [valueResult] at result
        | reject failure rejected => simp [valueResult] at result
        | ok value afterValue =>
            simp only [valueResult, pure] at result
            cases result
            exact .present equal.span
              (symbol_success_exactTokenParses .equal .contractMember
                equalResult)
              (expressionSound diagnosticFree valueResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .equal absent)

/-- Optional-initializer grammar soundness composes with source validity. -/
theorem optionalFieldInitializer_success_sound_and_validFor
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    {input next : State} {initializer : Option Expr}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalFieldInitializer expression input =
      .ok initializer next) :
    DeclarativeGrammar.OptionalContractFieldInitializerParses
        expressionParses input.declarativeRemainder initializer
          next.declarativeRemainder ∧
      Option.ValidFor expressionValueValid input.file initializer := by
  refine ⟨optionalFieldInitializer_success_sound expression
    expressionParses expressionSound diagnosticFree result,
    ?_⟩
  have valid := optionalFieldInitializer_validFor expression
    expressionValueValid expressionValid input inputValid
  rw [result] at valid
  exact valid.1

/-- Contract-field parsing reflects diagnostic freedom whenever initializer
expressions do. -/
theorem contractField_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (contractField expression) := by
  unfold contractField
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .contractMember)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .colon .contractMember)
  intro colon
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    typeExpr_reflectsDiagnosticFreeOnSuccess
  intro type
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalFieldInitializer_reflectsDiagnosticFreeOnSuccess expression
      expressionReflects)
  intro initializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .contractMember)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every diagnostic-free field success follows the exact name, type,
initializer, and semicolon grammar. -/
theorem contractField_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    {input next : State} {field : ContractField}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractField expression input = .ok field next) :
    DeclarativeGrammar.ContractFieldParses expressionParses
      input.declarativeRemainder field next.declarativeRemainder := by
  unfold contractField at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨colon, afterColon, colonResult, rest⟩
  rcases bind_ok_components rest with
    ⟨type, afterType, typeResult, rest⟩
  rcases bind_ok_components rest with
    ⟨initializer, afterInitializer, initializerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have afterInitializerFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .contractMember afterInitializer semicolon next
      semicolonResult diagnosticFree
  exact .parsed colon.span semicolon.span
    (identifier_success_sound .contractMember nameResult)
    (symbol_success_exactTokenParses .colon .contractMember colonResult)
    (typeExpr_success_sound typeResult)
    (optionalFieldInitializer_success_sound expression expressionParses
      expressionSound afterInitializerFree initializerResult)
    (symbol_success_exactTokenParses .semicolon .contractMember
      semicolonResult)

/-- Parametric field grammar soundness composes with source validity. -/
theorem contractField_success_sound_and_validFor
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionValueValid : SourceFile → Expr → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    {input next : State} {field : ContractField}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractField expression input = .ok field next) :
    DeclarativeGrammar.ContractFieldParses expressionParses
        input.declarativeRemainder field next.declarativeRemainder ∧
      ContractField.ValidFor expressionValueValid input.file field := by
  refine ⟨contractField_success_sound expression expressionParses
    expressionSound diagnosticFree result, ?_⟩
  have valid := contractField_validFor expression expressionValueValid
    expressionValid expressionWindow expressionCursor input inputValid
  rw [result] at valid
  exact valid.1

end ContractInternals

end Solcore.Syntax.Parser
