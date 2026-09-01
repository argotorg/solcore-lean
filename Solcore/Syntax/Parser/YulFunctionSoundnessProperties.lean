import Solcore.Syntax.DeclarativeYulFunctionGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedAllowEmptyDiagnosticFreeSoundnessProperties
import Solcore.Syntax.Parser.YulBlockSoundnessProperties
import Solcore.Syntax.Parser.YulFunctionDiagnosticReflectionProperties
import Solcore.Syntax.Parser.YulNamesSoundnessProperties

/-! Exact diagnostic-free soundness for inline-Yul functions. -/

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

/-- Every diagnostic-free Yul parameter-list success follows the exact
allow-empty, trailing-comma name grammar. -/
theorem yulParameters_success_sound {input next : State}
    {parameters : DelimitedList YulIdentifier}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulParameters input = .ok parameters next) :
    DeclarativeGrammar.YulParametersParses input.declarativeRemainder
      parameters next.declarativeRemainder := by
  unfold DeclarativeGrammar.YulParametersParses
  exact delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
    .leftParen .rightParen yulName DeclarativeGrammar.YulNameParses
    .yulStatement .yul
    (fun outputFree parsed =>
      yulName_success_sound_of_diagnosticFree outputFree parsed)
    yulName_reflectsDiagnosticFreeOnSuccess yulName_preservesTokenWindow
    diagnosticFree result

namespace YulControl

/-- Every diagnostic-free return clause retains its arrow, forward names,
covering span, and exact remainder. -/
theorem returnClause_success_sound {input next : State}
    {clause : YulReturnClause} (diagnosticFree : next.diagnosticsRev = [])
    (result : returnClause input = .ok clause next) :
    DeclarativeGrammar.YulReturnClauseParses input.declarativeRemainder clause
      next.declarativeRemainder := by
  unfold returnClause at result
  rcases bind_ok_components result with
    ⟨arrow, afterArrow, arrowResult, namesStage⟩
  rcases bind_ok_components namesStage with
    ⟨names, afterNames, namesResult, finished⟩
  cases finished
  exact .parsed arrow.span names.span
    (symbol_success_exactTokenParses .arrow .yulStatement arrowResult)
    (yulNames_success_sound diagnosticFree namesResult)

/-- Every optional-return success retains the preferred arrow branch or exact
arrow absence. -/
theorem returns_success_sound {input next : State}
    {returnsValue : Option YulReturnClause}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : returns input = .ok returnsValue next) :
    DeclarativeGrammar.YulReturnsParses input.declarativeRemainder returnsValue
      next.declarativeRemainder := by
  unfold returns getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨clause, afterClause, clauseResult, finished⟩
    cases finished
    exact .present (returnClause_success_sound diagnosticFree clauseResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .arrow absent)

end YulControl

/-- Every diagnostic-free Yul function success follows its exact signature,
optional returns, recursive body, cover span, AST, and remainder. -/
theorem yulFunctionStatement_success_sound
    (statement : Parser YulStmt)
    (statementParses : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : YulStmt},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : YulStmt}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulFunctionStatement statement input = .ok value next) :
    DeclarativeGrammar.YulFunctionStatementParses statementParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold yulFunctionStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, parametersStage⟩
  rcases bind_ok_components parametersStage with
    ⟨parameters, afterParameters, parametersResult, returnsStage⟩
  rcases bind_ok_components returnsStage with
    ⟨returnsValue, afterReturns, returnsResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterReturnsFree := yulBlock_reflectsDiagnosticFreeOnSuccess statement
    statementReflects afterReturns body next bodyResult diagnosticFree
  have afterParametersFree := YulControl.returns_reflectsDiagnosticFreeOnSuccess
    afterParameters returnsValue afterReturns returnsResult afterReturnsFree
  have afterNameFree := yulParameters_reflectsDiagnosticFreeOnSuccess afterName
    parameters afterParameters parametersResult afterParametersFree
  exact .parsed marker.span body.span
    (keyword_success_exactTokenParses .functionKw .yulStatement markerResult)
    (yulName_success_sound_of_diagnosticFree afterNameFree nameResult)
    (yulParameters_success_sound afterParametersFree parametersResult)
    (YulControl.returns_success_sound afterReturnsFree returnsResult)
    (yulBlock_success_sound statement statementParses statementReflects
      statementSound diagnosticFree bodyResult)

end Solcore.Syntax.Parser
