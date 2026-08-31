import Solcore.Syntax.Parser.Yul.StatementFallbackFuelTotalityProperties

/-! Fuel-aware totality for Yul statement recovery and its outer layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulRecoveryAdvance_state_shape {input next : State}
    {token : Token} (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

/-- More fuel than remaining tokens makes statement recovery succeed. -/
theorem recoverYulStatementAux_exists_ok_of_remainingCount_lt
    (first last : SourceSpan) :
    ∀ fuel input, input.remainingCount < fuel →
      ∃ statement final,
        recoverYulStatementAux first last fuel input = .ok statement final := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro input adequate
      omega
  | succ fuel inductionHypothesis =>
      intro input adequate
      unfold recoverYulStatementAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : input.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ statement final,
              recoverYulStatementAux first token.span fuel next =
                .ok statement final
            apply inductionHypothesis token.span next
            unfold State.advance? at advanced
            cases found : input.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at adequate ⊢
                omega

/-- Adequately fueled statement recovery has an ordinary success result. -/
theorem recoverYulStatementAux_ordinary_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel) :
    (∃ statement final,
      recoverYulStatementAux first last fuel input = .ok statement final) ∨
    (∃ failure final,
      recoverYulStatementAux first last fuel input = .reject failure final) :=
  Or.inl (recoverYulStatementAux_exists_ok_of_remainingCount_lt first last
    fuel input adequate)

/-- The production-selected statement recovery fuel is always sufficient. -/
theorem recoverYulStatementAux_production_exists_ok
    (first last : SourceSpan) (input : State) :
    ∃ statement final,
      recoverYulStatementAux first last (input.remainingCount + 1) input =
        .ok statement final :=
  recoverYulStatementAux_exists_ok_of_remainingCount_lt first last
    (input.remainingCount + 1) input (by omega)

theorem recoverYulStatementAux_production_ordinary
    (first last : SourceSpan) :
    Parser.Ordinary (fun input =>
      recoverYulStatementAux first last (input.remainingCount + 1) input) := by
  intro input
  exact Or.inl (recoverYulStatementAux_production_exists_ok first last input)

theorem recoverYulStatementAux_production_invariantFreeOnValid
    (first last : SourceSpan) :
    Parser.InvariantFreeOnValid (fun input =>
      recoverYulStatementAux first last (input.remainingCount + 1) input) :=
  (recoverYulStatementAux_production_ordinary first last).invariantFreeOnValid

theorem recoverYulStatementAux_production_ne_invariant
    (first last : SourceSpan) (input : State) (error : ParserInvariantError) :
    recoverYulStatementAux first last (input.remainingCount + 1) input ≠
      .invariant error :=
  (recoverYulStatementAux_production_ordinary first last).ne_invariant input
    error

theorem recoverYulStatementAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel) (error : ParserInvariantError) :
    recoverYulStatementAux first last fuel input ≠ .invariant error := by
  intro failed
  rcases recoverYulStatementAux_exists_ok_of_remainingCount_lt first last
      fuel input adequate with ⟨statement, final, result⟩
  rw [result] at failed
  contradiction

/-- Recovery adds no invariant after an ordinary terminated rejection. -/
theorem yulStatementLayer_ordinary_of_terminatedFuel
    (nested : Parser YulStmt) (fuel : Nat)
    (contract : FuelYulStatementTotalityContract
      (yulStatementTerminated nested) fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel) :
    (∃ statement next, yulStatementLayer nested input = .ok statement next) ∨
    (∃ failure next,
      yulStatementLayer nested input = .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨statement, next, terminatedResult⟩ |
    ⟨failure, failedState, terminatedResult⟩
  · exact Or.inl ⟨statement, next, by
      simp only [yulStatementLayer, terminatedResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : rewound.atEnd || isSymbol rewound .rightBrace
    · exact Or.inr ⟨failure, rewound, by
        simp only [yulStatementLayer, terminatedResult, rewound, boundary,
          ↓reduceIte]⟩
    · cases advanced : rewound.advance? with
      | none => exact Or.inr ⟨failure, rewound, by
          simp only [yulStatementLayer, terminatedResult, rewound, boundary,
            Bool.false_eq_true, ↓reduceIte, advanced]⟩
      | some pair =>
          rcases pair with ⟨token, afterToken⟩
          rcases recoverYulStatementAux_production_exists_ok token.span
              token.span (afterToken.emit failure.toDiagnostic) with
            ⟨recovered, final, recoveredResult⟩
          have recoveredAtProductionFuel :
              recoverYulStatementAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic) =
                  .ok recovered final := by
            have emitRemaining :
                (afterToken.emit failure.toDiagnostic).remainingCount =
                  afterToken.remainingCount := rfl
            rw [emitRemaining] at recoveredResult
            exact recoveredResult
          exact Or.inl ⟨recovered, final, by
            simp only [yulStatementLayer, terminatedResult, rewound, boundary,
              Bool.false_eq_true, ↓reduceIte, advanced,
              recoveredAtProductionFuel]⟩

theorem yulStatementLayer_ne_invariant_of_terminatedFuel
    (nested : Parser YulStmt) (fuel : Nat)
    (contract : FuelYulStatementTotalityContract
      (yulStatementTerminated nested) fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel) (error : ParserInvariantError) :
    yulStatementLayer nested input ≠ .invariant error := by
  intro failed
  rcases yulStatementLayer_ordinary_of_terminatedFuel nested fuel contract
      input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Layer success is strict when ordinary terminated success is strict. -/
theorem yulStatementLayer_cursor_lt_onSuccess_of_terminated
    (nested : Parser YulStmt)
    (terminatedStrict : ∀ {input final : State} {value : YulStmt},
      yulStatementTerminated nested input = .ok value final →
        input.cursor < final.cursor)
    {input final : State} {value : YulStmt}
    (parsed : yulStatementLayer nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulStatementLayer at parsed
  cases terminatedResult : yulStatementTerminated nested input with
  | invariant error => simp [terminatedResult] at parsed
  | ok statement next =>
      simp only [terminatedResult] at parsed
      cases parsed
      exact terminatedStrict terminatedResult
  | reject failure failedState =>
      simp only [terminatedResult] at parsed
      let rewound := { failedState with cursor := input.cursor }
      split at parsed
      · contradiction
      · cases advanced : rewound.advance? with
        | none =>
            rw [advanced] at parsed
            contradiction
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            rw [advanced] at parsed
            have recovered :=
              recoverYulStatementAux_cursorMonotoneOnSuccess token.span
                token.span (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic) value final parsed
            have shape := yulRecoveryAdvance_state_shape advanced
            exact Nat.lt_of_lt_of_le (by
              simp [shape, State.emit, rewound]) recovered

/-- Package one recovering layer with its complete bounded contract. -/
theorem yulStatementLayer_fuelTotalityContract
    (nested : Parser YulStmt) (fuel : Nat)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested))
    (terminatedContract : FuelYulStatementTotalityContract
      (yulStatementTerminated nested) fuel) :
    FuelYulStatementTotalityContract (yulStatementLayer nested) fuel := {
  toYulStatementParserContracts := {
    validFor := yulStatementLayer_validFor nested nestedValid nestedPreserves
      coreShape
    preservesTokens := yulStatementLayer_preservesTokensOnSuccess nested
      coreShape
    cursorMonotone := yulStatementLayer_cursorMonotoneOnSuccess nested
      nestedValid nestedPreserves
    startsAtToken := yulStatementLayer_startsAtCurrentTokenOnSuccess nested
      nestedValid nestedPreserves coreShape
  }
  preservesTokenWindow := yulStatementLayer_preservesTokenWindow nested
    coreShape
  ordinary := yulStatementLayer_ordinary_of_terminatedFuel nested fuel
    terminatedContract
}

end Solcore.Syntax.Parser
