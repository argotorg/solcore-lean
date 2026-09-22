import Solcore.Frontend.SourceRuntime

/-! Inversions of successful source-graph inference for primitive operations. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

theorem Expr.InfersType.unary_components
    {program : Program} {context : StaticContext}
    {op : Core.UnaryOp} {operand : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context (.unary op operand) expected) :
    Expr.InfersType program context operand op.operandType ∧
      expected = op.resultType := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases operandResult : infer program context operand with
  | error error =>
      simp [operandResult, bind, Except.bind] at inferredAt
  | ok operandType =>
      by_cases equal : operandType.erase = op.operandType
      · simp [operandResult, checkExpected, equal, bind, Except.bind]
          at inferredAt
        cases inferredAt
        exact ⟨⟨operandType, operandResult, equal⟩,
          by simpa [StaticType.erase] using erased.symm⟩
      · simp [operandResult, checkExpected, equal, bind, Except.bind]
          at inferredAt

theorem Expr.InfersType.binary_components
    {program : Program} {context : StaticContext}
    {op : Core.BinaryOp} {left right : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context (.binary op left right) expected) :
    Expr.InfersType program context left op.leftType ∧
      Expr.InfersType program context right op.rightType ∧
      expected = op.resultType := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases leftResult : infer program context left with
  | error error =>
      simp [leftResult, bind, Except.bind] at inferredAt
  | ok leftType =>
      by_cases leftMatches : leftType.erase = op.leftType
      · cases rightResult : infer program context right with
        | error error =>
            simp [leftResult, rightResult, checkExpected, leftMatches,
              bind, Except.bind] at inferredAt
            change Except.error error = Except.ok inferred at inferredAt
            cases inferredAt
        | ok rightType =>
            by_cases rightMatches : rightType.erase = op.rightType
            · simp [leftResult, rightResult, checkExpected, leftMatches,
                rightMatches, bind, Except.bind] at inferredAt
              cases inferredAt
              exact ⟨⟨leftType, leftResult, leftMatches⟩,
                ⟨rightType, rightResult, rightMatches⟩,
                by simpa [StaticType.erase] using erased.symm⟩
            · simp [leftResult, rightResult, checkExpected, leftMatches,
                rightMatches, bind, Except.bind] at inferredAt
              change Except.error (TypeError.typeMismatch op.rightType rightType.erase) =
                Except.ok inferred at inferredAt
              cases inferredAt
      · simp [leftResult, checkExpected, leftMatches, bind, Except.bind]
          at inferredAt

theorem Expr.InfersType.wordLt_components
    {program : Program} {context : StaticContext}
    {left right : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context (.wordLt left right) expected) :
    Expr.InfersType program context left .word ∧
      Expr.InfersType program context right .word ∧
      expected = .bool := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases leftResult : infer program context left with
  | error error =>
      simp [leftResult, bind, Except.bind] at inferredAt
  | ok leftType =>
      by_cases leftMatches : leftType.erase = Core.Ty.word
      · cases rightResult : infer program context right with
        | error error =>
            simp [leftResult, rightResult, checkExpected, leftMatches,
              bind, Except.bind] at inferredAt
            change Except.error error = Except.ok inferred at inferredAt
            cases inferredAt
        | ok rightType =>
            by_cases rightMatches : rightType.erase = Core.Ty.word
            · simp [leftResult, rightResult, checkExpected, leftMatches,
                rightMatches, bind, Except.bind] at inferredAt
              cases inferredAt
              exact ⟨⟨leftType, leftResult, leftMatches⟩,
                ⟨rightType, rightResult, rightMatches⟩,
                by simpa [StaticType.erase] using erased.symm⟩
            · simp [leftResult, rightResult, checkExpected, leftMatches,
                rightMatches, bind, Except.bind] at inferredAt
              change Except.error (TypeError.typeMismatch .word rightType.erase) =
                Except.ok inferred at inferredAt
              cases inferredAt
      · simp [leftResult, checkExpected, leftMatches, bind, Except.bind]
          at inferredAt

theorem Expr.InfersType.ifE_components
    {program : Program} {context : StaticContext}
    {condition thenBranch elseBranch : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context
      (.ifE condition thenBranch elseBranch) expected) :
    Expr.InfersType program context condition .bool ∧
      Expr.InfersType program context thenBranch expected ∧
      Expr.InfersType program context elseBranch expected := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  cases conditionResult : infer program context condition with
  | error error =>
      simp [conditionResult, bind, Except.bind] at inferredAt
  | ok conditionType =>
      by_cases conditionMatches : conditionType.erase = Core.Ty.bool
      · cases thenResult : infer program context thenBranch with
        | error error =>
            simp [conditionResult, thenResult, checkExpected,
              conditionMatches, bind, Except.bind] at inferredAt
            change Except.error error = Except.ok inferred at inferredAt
            cases inferredAt
        | ok thenType =>
            cases elseResult : infer program context elseBranch with
            | error error =>
                simp [conditionResult, thenResult, elseResult,
                  checkExpected, conditionMatches, bind, Except.bind]
                  at inferredAt
                change Except.error error = Except.ok inferred at inferredAt
                cases inferredAt
            | ok elseType =>
                by_cases sameType : thenType = elseType
                · subst elseType
                  simp [conditionResult, thenResult, elseResult,
                    checkExpected, conditionMatches,
                    bind, Except.bind] at inferredAt
                  change Except.ok thenType = Except.ok inferred at inferredAt
                  have inferredEq : inferred = thenType :=
                    Except.ok.inj inferredAt.symm
                  subst inferred
                  exact ⟨⟨conditionType, conditionResult,
                    conditionMatches⟩,
                    ⟨thenType, thenResult, erased⟩,
                    ⟨thenType, elseResult, erased⟩⟩
                · by_cases sameErased : thenType.erase = elseType.erase
                  · simp [conditionResult, thenResult, elseResult,
                      checkExpected, conditionMatches, sameType,
                      sameErased, bind, Except.bind] at inferredAt
                    change Except.ok (.value elseType.erase) =
                      Except.ok inferred at inferredAt
                    have inferredEq : inferred = .value elseType.erase :=
                      Except.ok.inj inferredAt.symm
                    subst inferred
                    have elseErased : elseType.erase = expected := by
                      simpa [StaticType.erase] using erased
                    have thenErased : thenType.erase = expected :=
                      sameErased.trans elseErased
                    exact ⟨⟨conditionType, conditionResult,
                      conditionMatches⟩,
                      ⟨thenType, thenResult, thenErased⟩,
                      ⟨elseType, elseResult, elseErased⟩⟩
                  · simp [conditionResult, thenResult, elseResult,
                      checkExpected, conditionMatches, sameType,
                      sameErased, bind, Except.bind] at inferredAt
                    change Except.error (TypeError.typeMismatch
                      thenType.erase elseType.erase) =
                      Except.ok inferred at inferredAt
                    cases inferredAt
      · simp [conditionResult, checkExpected, conditionMatches,
          bind, Except.bind] at inferredAt

theorem Expr.InfersType.letE_components
    {program : Program} {context : StaticContext}
    {binder : Resolved.LocalId} {value body : Expr} {expected : Core.Ty}
    (typing : Expr.InfersType program context
      (.letE binder value body) expected) :
    ∃ boundType,
      Expr.InfersType program context value boundType.erase ∧
      Expr.InfersType program ((binder, boundType) :: context) body expected := by
  obtain ⟨inferred, inferredAt, erased⟩ := typing
  unfold infer at inferredAt
  split at inferredAt
  · simp [bind, Except.bind] at inferredAt
  · cases valueResult : infer program context value with
    | error error =>
        simp [valueResult, bind, Except.bind] at inferredAt
    | ok boundType =>
        cases bodyResult : infer program ((binder, boundType) :: context) body with
        | error error =>
            simp [valueResult, bodyResult, bind, Except.bind] at inferredAt
        | ok bodyType =>
            simp [valueResult, bodyResult, bind, Except.bind] at inferredAt
            have inferredEq : inferred = bodyType :=
              inferredAt.symm
            subst inferred
            exact ⟨boundType,
              ⟨boundType, valueResult, rfl⟩,
              ⟨bodyType, bodyResult, erased⟩⟩

end Solcore.Frontend.SourceRuntime
