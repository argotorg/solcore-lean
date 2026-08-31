import Solcore.Syntax.Parser.Parameter
import Solcore.Syntax.Parser.TypeRecursiveProperties

/-! Token-window contracts for recovering function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace FunctionParameterInternals

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

private theorem getState_preservesTokenWindowForParameter :
    Parser.PreservesTokenWindow getState := fun _ => ⟨rfl, rfl⟩

private theorem emitDiagnostic_preservesTokenWindowForParameter
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokenWindow (emitDiagnostic diagnostic) := by
  intro input
  unfold emitDiagnostic modifyState Reply.PreservesTokenWindow
  exact ⟨rfl, rfl⟩

theorem finishTypedParameter_preservesTokenWindow (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) :
    Parser.PreservesTokenWindow
      (finishTypedParameter start comptimeMarker name type) := by
  unfold finishTypedParameter
  split
  · apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindowForParameter _)
    intro _
    exact Parser.pure_preservesTokenWindow _
  · exact Parser.pure_preservesTokenWindow _

theorem errorParameter_preservesTokenWindow (span : SourceSpan)
    (constraint : ParseConstraint) :
    Parser.PreservesTokenWindow (errorParameter span constraint) := by
  unfold errorParameter
  apply Parser.bind_preservesTokenWindow
    (emitDiagnostic_preservesTokenWindowForParameter _)
  intro _
  exact Parser.pure_preservesTokenWindow _

theorem ordinaryNamedParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow ordinaryNamedParameter := by
  unfold ordinaryNamedParameter
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .parameter)
  intro name
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true]
    apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindowForParameter _)
    intro _
    apply Parser.bind_preservesTokenWindow
      getState_preservesTokenWindowForParameter
    intro observed
    by_cases typed : isSymbol observed .colon
    · simp only [typed, if_true]
      apply Parser.bind_preservesTokenWindow
        (symbol_preservesTokenWindow .colon .parameter)
      intro _
      apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
      intro type
      exact finishTypedParameter_preservesTokenWindow name.span none name type
    · simp only [typed]
      exact errorParameter_preservesTokenWindow name.span _
  · simp only [warned]
    apply Parser.bind_preservesTokenWindow
      getState_preservesTokenWindowForParameter
    intro observed
    by_cases typed : isSymbol observed .colon
    · simp only [typed, if_true]
      apply Parser.bind_preservesTokenWindow
        (symbol_preservesTokenWindow .colon .parameter)
      intro _
      apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
      intro type
      exact finishTypedParameter_preservesTokenWindow name.span none name type
    · simp only [typed]
      exact errorParameter_preservesTokenWindow name.span _

theorem comptimeNamedParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow comptimeNamedParameter := by
  unfold comptimeNamedParameter
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .comptime .parameter)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .parameter)
  intro name
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindowForParameter
  intro observed
  by_cases typed : isSymbol observed .colon
  · simp only [typed, if_true]
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .colon .parameter)
    intro _
    apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
    intro type
    exact finishTypedParameter_preservesTokenWindow marker.span
      (some marker.span) name type
  · simp only [typed]
    exact errorParameter_preservesTokenWindow
      (SourceSpan.cover marker.span name.span) _

theorem namedParameterCore_preservesTokenWindow :
    Parser.PreservesTokenWindow namedParameterCore := by
  intro input
  unfold namedParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeNamedParameter_preservesTokenWindow input
    · exact ordinaryNamedParameter_preservesTokenWindow input
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryNamedParameter_preservesTokenWindow input

theorem recoverParameterAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow (recoverParameterAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverParameterAux
      split
      · unfold finishRecoveredParameter Reply.PreservesTokenWindow
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecoveredParameter Reply.PreservesTokenWindow
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            exact (inductionHypothesis token.span afterToken).trans (by
              simp [advance?_state_shape advanced])

theorem recoverParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverParameter := by
  intro input
  unfold recoverParameter
  cases advanced : input.advance? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      exact (recoverParameterAux_preservesTokenWindow token.span token.span
        (afterToken.remainingCount + 1) afterToken).trans (by
          simp [advance?_state_shape advanced])

end FunctionParameterInternals

/-- Function-parameter parsing preserves every ordinary token window. -/
theorem namedParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow namedParameter := by
  intro input
  unfold namedParameter
  have coreShape :=
    FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok parameter next => rw [coreResult] at coreShape; exact coreShape
  | invariant error => trivial
  | reject failure failedState =>
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := ⟨by simp [rewound, coreShape.1],
        by simp [rewound, coreShape.2]⟩
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then Reply.reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)).PreservesTokenWindow input
      split
      · exact rewoundShape
      · exact (FunctionParameterInternals.recoverParameter_preservesTokenWindow
          (rewound.emit failure.toDiagnostic)).trans (by
            simpa [State.emit] using rewoundShape)

/-- Successful function-parameter parsing retains the token carrier. -/
theorem namedParameter_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess namedParameter :=
  namedParameter_preservesTokenWindow.preservesTokensOnSuccess

end Solcore.Syntax.Parser
