import Solcore.Syntax.DeclarativeTypeAliasValueOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.TypeAliasRecoveryTotalityProperties

/-! Exact executable ordinary outcomes for type-alias value recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem isSymbol_eq_true_of_tokenAt (value : Symbol)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value }) :
    isSymbol input value = true := by
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem tokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .typeAlias present with
    ⟨token, parsed⟩
  exact ⟨token.span, (symbol_ok_tokenAt value .typeAlias parsed).1⟩

/-- A true executable entry guard gives the exact non-consuming recovery
boundary. -/
theorem typeAliasValueBoundaryStops_of_guard_eq_true
    (input : State)
    (boundary : (input.atEnd || isSymbol input .semicolon) = true) :
    DeclarativeGrammar.TypeAliasValueBoundaryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have semicolon : isSymbol input .semicolon = true := by
      simpa [atEndFalse] using boundary
    exact .semicolon
      (tokenAt_of_isSymbol_eq_true .semicolon semicolon).choose_spec

/-- A false executable entry guard excludes every non-consuming recovery
boundary. -/
theorem no_typeAliasValueBoundaryStops_of_guard_eq_false
    (input : State)
    (boundary : (input.atEnd || isSymbol input .semicolon) = false) :
    ¬ DeclarativeGrammar.TypeAliasValueBoundaryStops
      input.declarativeRemainder := by
  intro stops
  cases stops with
  | windowEnd atEnd =>
      have atEndTrue : input.atEnd = true := by
        unfold State.atEnd
        exact decide_eq_true atEnd
      simp [atEndTrue] at boundary
  | semicolon present =>
      have semicolon : isSymbol input .semicolon = true :=
        isSymbol_eq_true_of_tokenAt .semicolon (by
          simpa [State.declarativeRemainder] using present)
      simp [semicolon] at boundary

private theorem typeAliasValueRecoveryStops_of_guard_eq_true
    (input : State)
    (boundary : (input.atEnd || isSymbol input .semicolon) = true) :
    DeclarativeGrammar.TypeAliasValueRecoveryStops
      input.declarativeRemainder := by
  have stops := typeAliasValueBoundaryStops_of_guard_eq_true input boundary
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | semicolon token => exact .semicolon token

private theorem typeAliasValueRecoveryStops_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.TypeAliasValueRecoveryStops
      input.declarativeRemainder := by
  by_cases boundary : (input.atEnd || isSymbol input .semicolon) = true
  · exact typeAliasValueRecoveryStops_of_guard_eq_true input boundary
  · have boundaryFalse :
        (input.atEnd || isSymbol input .semicolon) = false :=
      Bool.eq_false_iff.mpr boundary
    have notAtEnd : ¬ input.window.endIndex ≤ input.cursor := by
      intro atEnd
      have atEndTrue : input.atEnd = true := by
        unfold State.atEnd
        exact decide_eq_true atEnd
      simp [atEndTrue] at boundaryFalse
    have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.TypeAliasValueRecoveryStops.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

private theorem no_typeAliasValueRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : (input.atEnd || isSymbol input .semicolon) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.TypeAliasValueRecoveryStops
      input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | semicolon present =>
      have semicolon : isSymbol input .semicolon = true :=
        isSymbol_eq_true_of_tokenAt .semicolon (by
          simpa [State.declarativeRemainder] using present)
      simp [semicolon] at boundary
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

namespace TypeAliasInternals

/-- Every successful executable auxiliary scan records exact boundary
priority, consumed tokens, recovered span, and final remainder. -/
theorem recoverTypeAliasValueAux_success_ordinary_sound
    (first : SourceSpan) :
    ∀ fuel last input value output,
      recoverTypeAliasValueAux first last fuel input = .ok value output →
      DeclarativeGrammar.TypeAliasValueRecoveryScanParses first last
        input.declarativeRemainder value output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input value output result
      simp [recoverTypeAliasValueAux] at result
  | succ fuel inductionHypothesis =>
      intro last input value output result
      unfold recoverTypeAliasValueAux at result
      by_cases boundary :
          (input.atEnd || isSymbol input .semicolon) = true
      · simp only [boundary, if_true] at result
        unfold finishRecoveredType at result
        cases result
        simpa [State.emit, State.declarativeRemainder] using
          (DeclarativeGrammar.TypeAliasValueRecoveryScanParses.stop
            (first := first) (last := last)
            (typeAliasValueRecoveryStops_of_guard_eq_true input boundary))
      · have boundaryFalse :
            (input.atEnd || isSymbol input .semicolon) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredType at result
            cases result
            simpa [State.emit, State.declarativeRemainder] using
              (DeclarativeGrammar.TypeAliasValueRecoveryScanParses.stop
                (first := first) (last := last)
                (typeAliasValueRecoveryStops_of_advance?_eq_none input
                  advanced))
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next value output result
            rw [nextEq] at tail
            exact .next
              (no_typeAliasValueRecoveryStops_of_nonBoundary_token
                boundaryFalse found)
              (tokenAt_of_peek?_eq_some found) tail

/-- Every successful recovery consumes its mandatory first token and then
follows the exact semicolon-preserving scan. -/
theorem recoverTypeAliasValue_success_ordinary_sound
    {input output : State} {value : TypeExpr}
    (result : recoverTypeAliasValue input = .ok value output) :
    DeclarativeGrammar.TypeAliasValueRecoveryParses
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold recoverTypeAliasValue at result
  by_cases boundary : (input.atEnd || isSymbol input .semicolon) = true
  · simp [boundary, rejectAt] at result
  · have boundaryFalse :
        (input.atEnd || isSymbol input .semicolon) = false :=
      Bool.eq_false_iff.mpr boundary
    simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
    cases advanced : input.advance? with
    | none => simp [advanced, rejectAt] at result
    | some pair =>
        rcases pair with ⟨token, next⟩
        simp only [advanced] at result
        rcases advance?_state_shape advanced with ⟨found, nextEq⟩
        have scan := recoverTypeAliasValueAux_success_ordinary_sound token.span
          (next.remainingCount + 1) token.span next value output result
        rw [nextEq] at scan
        exact .recovered
          (no_typeAliasValueBoundaryStops_of_guard_eq_false input
            boundaryFalse)
          (tokenAt_of_peek?_eq_some found) scan

/-- Every recovery rejection is the exact non-consuming entry boundary or a
missing mandatory carrier token. -/
theorem recoverTypeAliasValue_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : recoverTypeAliasValue input = .reject failure rejected) :
    DeclarativeGrammar.TypeAliasValueRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverTypeAliasValue at result
  by_cases boundary : (input.atEnd || isSymbol input .semicolon) = true
  · simp only [boundary, if_true] at result
    unfold rejectAt at result
    cases result
    exact .boundary
      (typeAliasValueBoundaryStops_of_guard_eq_true input boundary)
  · have boundaryFalse :
        (input.atEnd || isSymbol input .semicolon) = false :=
      Bool.eq_false_iff.mpr boundary
    simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
    cases advanced : input.advance? with
    | none =>
        simp only [advanced] at result
        unfold rejectAt at result
        cases result
        have stops := typeAliasValueRecoveryStops_of_advance?_eq_none input
          advanced
        cases stops with
        | windowEnd atEnd =>
            have atEndTrue : input.atEnd = true := by
              unfold State.atEnd
              exact decide_eq_true atEnd
            simp [atEndTrue] at boundaryFalse
        | semicolon present =>
            have semicolon : isSymbol input .semicolon = true :=
              isSymbol_eq_true_of_tokenAt .semicolon (by
                simpa [State.declarativeRemainder] using present)
            simp [semicolon] at boundaryFalse
        | missingToken inside missing => exact .missingToken inside missing
    | some pair =>
        rcases pair with ⟨token, next⟩
        simp only [advanced] at result
        rcases recoverTypeAliasValueAux_production_exists_ok token.span
            token.span next with ⟨recovered, final, recoveredResult⟩
        rw [recoveredResult] at result
        contradiction

/-- Package standalone alias-value recovery success and rejection. -/
theorem recoverTypeAliasValue_ordinaryOutcome_sound :
    (∀ {input output : State} {value : TypeExpr},
      recoverTypeAliasValue input = .ok value output →
        DeclarativeGrammar.TypeAliasValueRecoveryParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverTypeAliasValue input = .reject failure rejected →
        DeclarativeGrammar.TypeAliasValueRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverTypeAliasValue_success_ordinary_sound,
    recoverTypeAliasValue_reject_ordinary_sound⟩

/-- Re-export deterministic standalone alias-value recovery outcomes. -/
theorem recoverTypeAliasValue_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasValueRecoveryParses
      DeclarativeGrammar.TypeAliasValueRecoveryRejects :=
  DeclarativeGrammar.typeAliasValueRecoveryDeterministicOutcomeSpec

end TypeAliasInternals
end Solcore.Syntax.Parser
