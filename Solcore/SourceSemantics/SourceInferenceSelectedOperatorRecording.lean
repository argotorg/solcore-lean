import Solcore.SourceSemantics.SourceInferenceSelectedOperatorTyping

/-! Primitive and trait operator tails consume the actual typed operands and
retained requirement sites in the final lexical context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem inferUnaryOperator_recordExpressionWithExpected_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.UnaryOp} {operand : InferredExpression}
    {expected : Option TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {operandState later : Frontend.SourceInference.State}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (operatorSuccess : Detail.inferUnaryOperator inferenceContext operator
      operand.type expected integerLiterals operandState = .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type (.unary operator operand.id)
      inferred.requirements expected inferred.state = .ok result)
    (operandType : ExpressionHasType semanticSource active operand.id
      (later.inference.substitution.apply operand.type))
    (operandReady : operandState.InferenceReady)
    (operandBelow : operand.type.VariablesBelow
      operandState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow operandState.inference.next)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ integerLiterals →
        later.inference.substitution.apply
            (.variable origin.metavariable) = .word ∨
          later.inference.substitution.apply
            (.variable origin.metavariable) = .integer)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (operatorsRetained : ExpressionOperatorSiteRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (activeCatalog : SignatureCatalogWellFormed active.signatures)
    (activeBinders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered evidenceSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots) semanticSource active
      later.inference.substitution result.1 := by
  have operatorProperties := Detail.inferUnaryOperator_inferenceProperties
    operandReady operandBelow expectedBelow operatorSuccess
  have inferenceCase : UnaryOperatorInferenceCase inferenceContext
      (Context.ofSignatures inferenceContext.signatures) operandState operator operand.type integerLiterals inferred :=
    inferUnaryOperator_success_case operatorSuccess
      operatorProperties.2.1.solved
  have expectedBelowInferred : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow inferred.state.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken operatorProperties.1.next_le
  have recordProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      operatorProperties.2.1 operatorProperties.2.2 expectedBelowInferred
      recordSuccess
  have inferredSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        inferred.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordProperties.1.substitution_extends
  have inferredRequirementsSubset :
      inferred.state.requirements ⊆ later.requirements :=
    List.Subset.trans
      (Detail.recordExpressionWithExpected_requirements_subset recordSuccess)
      requirementsSubset
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recordSuccess roots
  have operatorRequirementsOccur : ∀ requirement,
      requirement ∈ inferred.requirements →
        PrimaryRequirementOccursAt evidenceSource
          (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    simp [member]
  have operatorNames : OperatorNamesAt inferenceContext.signatures solved inferred.requirements
      (fun name => ∃ method, UnaryTraitDispatch operator name method) :=
    OperatorNamesAt.of_retained operatorsRetained interfaces recordedContains rfl (by
      intro name selected
      obtain ⟨method, dispatch⟩ := selected
      cases dispatch <;> exact ⟨_, rfl⟩)
  have operatorType : UnaryOperatorHasType active operator
      (later.inference.substitution.apply operand.type)
      (later.inference.substitution.apply inferred.type)
      inferred.requirements :=
    unaryOperatorInferenceCase_hasType_in_active inferenceCase
      operatorProperties.1 inferredSubstitutionExtends
      inferredRequirementsSubset
      integerLiteralTargetsSupported activeCatalog signaturesEq
      operatorNames solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered
      operatorRequirementsOccur
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.unary operator operand.id).applySubstitution
        later.inference.substitution)
      (later.inference.substitution.apply inferred.type)
      (.ordinary inferred.requirements) := by
    simpa [ExpressionForm.applySubstitution] using
      (ExpressionFormHasRawType.unary operandType operatorType)
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply inferred.type) :=
    operatorType.result_type_admissible activeCatalog activeBinders
      operandType.type_admissible
  exact
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      recordSuccess substitutionExtends requirementsSubset retained formType
      rawAdmissible interfaces coercionsRetained activeCatalog
      signaturesEq solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered


private theorem binaryOperatorHasType_operand_types_eq
    {context : SourceSemantics.Context} {operator : Syntax.BinaryOp}
    {left right result : TypeSystem.Ty}
    {requirements : List RequirementId}
    (typing : BinaryOperatorHasType context operator left right result
      requirements) :
    left = right := by
  cases typing <;> rfl


theorem inferBinaryOperator_recordExpressionWithExpected_typing_from_interfaces
    {inferenceContext solverContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.BinaryOp}
    {left right : InferredExpression}
    {expected : Option TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {operandState later : Frontend.SourceInference.State}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    (operatorSuccess : Detail.inferBinaryOperator inferenceContext operator
      left.type right.type expected integerLiterals operandState = .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type (.binary left.id operator right.id)
      inferred.requirements expected inferred.state = .ok result)
    (leftType : ExpressionHasType semanticSource active left.id
      (later.inference.substitution.apply left.type))
    (rightType : ExpressionHasType semanticSource active right.id
      (later.inference.substitution.apply right.type))
    (operandReady : operandState.InferenceReady)
    (leftBelow : left.type.VariablesBelow operandState.inference.next)
    (rightBelow : right.type.VariablesBelow operandState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow operandState.inference.next)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ integerLiterals →
        later.inference.substitution.apply
            (.variable origin.metavariable) = .word ∨
          later.inference.substitution.apply
            (.variable origin.metavariable) = .integer)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces inferenceContext.signatures solved evidenceSource)
    (coercionsRetained : ExpressionCoercionPrimariesRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (operatorsRetained : ExpressionOperatorSiteRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (activeCatalog : SignatureCatalogWellFormed active.signatures)
    (activeBinders : TypeParameterBindersWellFormed active)
    (signaturesEq : active.signatures = inferenceContext.signatures)
    (solveSuccess : Detail.solveRequirements solverContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered evidenceSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots) semanticSource active
      later.inference.substitution result.1 := by
  have operatorProperties := Detail.inferBinaryOperator_inferenceProperties
    operandReady leftBelow rightBelow expectedBelow operatorSuccess
  have inferenceCase : BinaryOperatorInferenceCase inferenceContext
      (Context.ofSignatures inferenceContext.signatures) operandState operator left.type right.type integerLiterals
      inferred :=
    inferBinaryOperator_success_case operatorSuccess
  have expectedBelowInferred : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow inferred.state.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken operatorProperties.1.next_le
  have recordProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      operatorProperties.2.1 operatorProperties.2.2 expectedBelowInferred
      recordSuccess
  have inferredSubstitutionExtends :
      later.inference.substitution.SemanticallyExtends
        inferred.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordProperties.1.substitution_extends
  have inferredRequirementsSubset :
      inferred.state.requirements ⊆ later.requirements :=
    List.Subset.trans
      (Detail.recordExpressionWithExpected_requirements_subset recordSuccess)
      requirementsSubset
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recordSuccess roots
  have operatorRequirementsOccur : ∀ requirement,
      requirement ∈ inferred.requirements →
        PrimaryRequirementOccursAt evidenceSource
          (.expression result.1.id) requirement := by
    intro requirement member
    apply retained recordedContains
    simp [member]
  have operatorNames : OperatorNamesAt inferenceContext.signatures solved inferred.requirements
      (fun name => ∃ method, BinaryTraitDispatch operator name method) :=
    OperatorNamesAt.of_retained operatorsRetained interfaces recordedContains rfl (by
      intro name selected
      obtain ⟨method, dispatch⟩ := selected
      cases dispatch <;> exact ⟨_, rfl⟩)
  have operatorType : BinaryOperatorHasType active operator
      (later.inference.substitution.apply left.type)
      (later.inference.substitution.apply right.type)
      (later.inference.substitution.apply inferred.type)
      inferred.requirements :=
    binaryOperatorInferenceCase_hasType_in_active inferenceCase
      operatorProperties.1 inferredSubstitutionExtends
      inferredRequirementsSubset
      integerLiteralTargetsSupported activeCatalog signaturesEq
      operatorNames solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered
      operatorRequirementsOccur
  have operandTypesEq :
      later.inference.substitution.apply left.type =
        later.inference.substitution.apply right.type :=
    binaryOperatorHasType_operand_types_eq operatorType
  have rightTypeAsLeft : ExpressionHasType semanticSource active right.id
      (later.inference.substitution.apply left.type) := by
    rw [operandTypesEq]
    exact rightType
  have operatorTypeAsLeft : BinaryOperatorHasType active operator
      (later.inference.substitution.apply left.type)
      (later.inference.substitution.apply left.type)
      (later.inference.substitution.apply inferred.type)
      inferred.requirements := by
    rwa [← operandTypesEq] at operatorType
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.binary left.id operator right.id).applySubstitution
        later.inference.substitution)
      (later.inference.substitution.apply inferred.type)
      (.ordinary inferred.requirements) := by
    simpa [ExpressionForm.applySubstitution] using
      (ExpressionFormHasRawType.binary leftType rightTypeAsLeft
        operatorTypeAsLeft)
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply inferred.type) :=
    operatorTypeAsLeft.result_type_admissible activeCatalog activeBinders
      leftType.type_admissible
  exact
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_from_interfaces
      recordSuccess substitutionExtends requirementsSubset retained formType
      rawAdmissible interfaces coercionsRetained activeCatalog
      signaturesEq solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered


end Solcore.SourceSemantics.SourceInferenceSoundness
