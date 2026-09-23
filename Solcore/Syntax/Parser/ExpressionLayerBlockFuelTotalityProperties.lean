import Solcore.Syntax.Parser.ExpressionLayerFuelContractProperties
import Solcore.Syntax.Parser.Expression.Atom
import Solcore.Syntax.Parser.Expression.LambdaTotalityProperties
import Solcore.Syntax.Parser.Expression.PostfixTailFuelTotalityProperties

/-! Fuel-aware expression layers whose lambda bodies are recursive blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- A lambda is ordinary when its body has enough fuel after `lam` advances. -/
theorem lambdaExpression_ordinary_of_blockFuel (block : Parser Block)
    (blockFuel : Nat)
    (blockContract : FuelElementTotalityContract block blockFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < blockFuel + 1) :
    (exists value next, lambdaExpression block input = .ok value next) ∨
      (exists failure next,
        lambdaExpression block input = .reject failure next) := by
  rcases (keyword_ordinary .lamKw .expression) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .lamKw .expression input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .lamKw .expression input
    rw [markerResult] at markerWindow
    have markerProgress := acceptToken_cursor_lt_onSuccess
      (.keyword .lamKw) .expression (· == .keyword .lamKw) markerResult
    have afterMarkerAdequate : afterMarker.remainingCount < blockFuel :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress adequate
    rcases delimited_ordinary .leftParen .rightParen true lambdaParameter
        .parameter .expression lambdaParameter_elementTotalityContract
        afterMarker markerReply.2.1 with
      ⟨parameters, afterParameters, parametersResult⟩ |
      ⟨failure, rejected, parametersResult⟩
    · have parametersReply := delimited_validFor LambdaParameter.ValidFor
        .leftParen .rightParen true lambdaParameter .parameter .expression
        lambdaParameter_validFor lambdaParameter_preservesTokensOnSuccess
        afterMarker markerReply.2.1
      rw [parametersResult] at parametersReply
      have parametersWindow := delimited_preservesTokenWindow .leftParen
        .rightParen true lambdaParameter .parameter .expression
        lambdaParameter_preservesTokenWindow afterMarker
      rw [parametersResult] at parametersWindow
      have parametersCursor := delimited_cursorMonotoneOnSuccess .leftParen
        .rightParen true lambdaParameter .parameter .expression afterMarker
        parameters afterParameters parametersResult
      have afterParametersAdequate :
          afterParameters.remainingCount < blockFuel :=
        remainingCount_lt_of_cursor_le parametersWindow.2 parametersCursor
          afterMarkerAdequate
      rcases optionalLambdaReturnType_invariantFreeOnValid afterParameters
          parametersReply.2.1 with
        ⟨returnType, afterReturnType, returnTypeResult⟩ |
        ⟨failure, rejected, returnTypeResult⟩
      · have returnTypeReply := optionalLambdaReturnType_validFor
          afterParameters parametersReply.2.1
        rw [returnTypeResult] at returnTypeReply
        have returnTypeWindow :=
          optionalLambdaReturnType_preservesTokenWindow afterParameters
        rw [returnTypeResult] at returnTypeWindow
        have returnTypeCursor :=
          optionalLambdaReturnType_cursorMonotoneOnSuccess afterParameters
            returnType afterReturnType returnTypeResult
        have bodyAdequate : afterReturnType.remainingCount < blockFuel :=
          remainingCount_lt_of_cursor_le returnTypeWindow.2 returnTypeCursor
            afterParametersAdequate
        rcases blockContract.ordinary afterReturnType returnTypeReply.2.1
            bodyAdequate with
          ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
        · exact Or.inl ⟨{
              span := SourceSpan.cover marker.span body.span
              value := .lambda marker.span parameters returnType body
            }, final, by
              simp only [lambdaExpression, bind, markerResult,
                parametersResult, returnTypeResult, bodyResult, pure]⟩
        · exact Or.inr ⟨failure, rejected, by
              simp only [lambdaExpression, bind, markerResult,
                parametersResult, returnTypeResult, bodyResult]⟩
      · exact Or.inr ⟨failure, rejected, by
            simp only [lambdaExpression, bind, markerResult,
              parametersResult, returnTypeResult]⟩
    · exact Or.inr ⟨failure, rejected, by
          simp only [lambdaExpression, bind, markerResult, parametersResult]⟩
  · exact Or.inr ⟨failure, rejected, by
        simp only [lambdaExpression, bind, markerResult]⟩

private theorem expressionAtomCore_ordinary_of_fuels
    (nested : Parser Expr) (block : Parser Block)
    (nestedFuel blockFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (blockContract : FuelElementTotalityContract block blockFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (blockAdequate : input.remainingCount < blockFuel + 1) :
    (exists value next,
      expressionAtomCore nested block input = .ok value next) ∨
    (exists failure next,
      expressionAtomCore nested block input = .reject failure next) := by
  unfold expressionAtomCore
  split
  · exact literalExpression_invariantFreeOnValid input inputValid
  · split
    · exact identifierExpression_invariantFreeOnValid input inputValid
    · split
      · exact dotConstructor_ordinary_of_elementFuel nested nestedFuel
          nestedContract input inputValid nestedAdequate
      · split
        · exact proxyExpression_invariantFreeOnValid input inputValid
        · split
          · exact parenthesized_ordinary_of_elementFuel nested nestedFuel
              nestedContract input inputValid nestedAdequate
          · split
            · exact arrayLiteral_ordinary_of_elementFuel nested nestedFuel
                nestedContract input inputValid nestedAdequate
            · split
              · exact lambdaExpression_ordinary_of_blockFuel block blockFuel
                  blockContract input inputValid blockAdequate
              · exact Parser.rejectAt_invariantFreeOnValid
                  { head := .expression, tail := [] } .expression input inputValid

private theorem expressionAtom_ordinary_of_fuels
    (nested : Parser Expr) (block : Parser Block)
    (nestedFuel blockFuel : Nat)
    (nestedContract : FuelElementTotalityContract nested nestedFuel)
    (blockContract : FuelElementTotalityContract block blockFuel)
    (input : State) (inputValid : input.ValidFor)
    (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (blockAdequate : input.remainingCount < blockFuel + 1) :
    (exists value next, expressionAtom nested block input = .ok value next) ∨
    (exists failure next,
      expressionAtom nested block input = .reject failure next) := by
  rcases expressionAtomCore_ordinary_of_fuels nested block nestedFuel
      blockFuel nestedContract blockContract input inputValid nestedAdequate
      blockAdequate with
    ⟨value, next, coreResult⟩ | ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨value, next, by simp [expressionAtom, coreResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : isAtomBoundary rewound
    · exact Or.inr ⟨failure, rewound, by
          simp [expressionAtom, coreResult, rewound, boundary]⟩
    · have boundaryFalse : isAtomBoundary rewound = false := by
        cases found : isAtomBoundary rewound with
        | false => rfl
        | true => exact False.elim (boundary found)
      rcases recoverAtom_ordinary (rewound.emit failure.toDiagnostic) with
        ⟨recovered, final, recoveryResult⟩ |
        ⟨recoveryFailure, rejected, recoveryResult⟩
      · exact Or.inl ⟨recovered, final, by
            simp [expressionAtom, coreResult, rewound, boundaryFalse,
              recoveryResult]⟩
      · exact Or.inr ⟨recoveryFailure, rejected, by
            simp [expressionAtom, coreResult, rewound, boundaryFalse,
              recoveryResult]⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser.ExpressionInternals

/-- Lift one expression layer while keeping lambda-block fuel explicit. -/
theorem expressionLayer_blockFuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (nested : Parser Expr) (block : Parser Block)
    (nestedFuel blockFuel : Nat)
    (nestedSyntax : ExpressionContract statementValid nested)
    (nestedTotality : FuelElementTotalityContract nested nestedFuel)
    (blockValid : block.ValidFor (Block.ValidFor statementValid))
    (blockWindow : Parser.PreservesTokenWindow block)
    (blockCursor : Parser.CursorMonotoneOnSuccess block)
    (blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span))
    (blockTotality : FuelElementTotalityContract block blockFuel) :
    FuelElementTotalityContract (expressionLayer nested block)
      (Nat.min nestedFuel blockFuel + 1) := by
  let commonFuel := Nat.min nestedFuel blockFuel
  let commonNested : FuelElementTotalityContract nested commonFuel :=
    nestedTotality.weaken (by
      exact Nat.min_le_left nestedFuel blockFuel)
  let atomSyntax := ExpressionContract.atom statementValid nested block
    nestedSyntax blockValid blockWindow blockCursor blockStarts
  let postfixSyntax := ExpressionContract.concretePostfix statementValid
    nested block nestedSyntax blockValid blockWindow blockCursor blockStarts
  have postfixTotality : FuelElementTotalityContract
      (expressionPostfix nested block) (commonFuel + 1) := {
    validFor := postfixSyntax.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := postfixSyntax.preservesTokenWindow
    cursorLtOnSuccess := postfixSyntax.cursorLtOnSuccess
    ordinary := by
      intro input inputValid adequate
      rcases ExpressionAtomInternals.expressionAtom_ordinary_of_fuels nested
          block commonFuel blockFuel commonNested blockTotality input inputValid
          adequate (Nat.lt_of_lt_of_le adequate (by
            exact Nat.add_le_add_right
              (Nat.min_le_right nestedFuel blockFuel) 1)) with
        ⟨base, next, atomResult⟩ | ⟨failure, rejected, atomResult⟩
      · have atomReply := atomSyntax.validFor input inputValid
        rw [atomResult] at atomReply
        have atomWindow := atomSyntax.preservesTokenWindow input
        rw [atomResult] at atomWindow
        have nextAdequate : next.remainingCount < commonFuel + 1 :=
          remainingCount_lt_of_cursor_le atomWindow.2
            (Nat.le_of_lt (atomSyntax.cursorLtOnSuccess atomResult)) adequate
        rcases ExpressionAtomInternals.postfixTail_production_ordinary nested
            block commonFuel commonNested base next atomReply.2.1
            nextAdequate with
          ⟨value, final, tailResult⟩ | ⟨failure, rejected, tailResult⟩
        · exact Or.inl ⟨value, final, by
              simp [expressionPostfix, atomResult, tailResult]⟩
        · exact Or.inr ⟨failure, rejected, by
              simp [expressionPostfix, atomResult, tailResult]⟩
      · exact Or.inr ⟨failure, rejected, by
            simp [expressionPostfix, atomResult]⟩
  }
  simpa only [commonFuel] using expressionLayer_fuelTotalityContract nested
    block commonFuel nestedSyntax postfixSyntax commonNested postfixTotality

end Solcore.Syntax.Parser.ExpressionInternals
