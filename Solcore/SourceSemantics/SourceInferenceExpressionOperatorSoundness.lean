import Solcore.SourceSemantics.SourceInferenceExpressionCallDispatchSoundness

/-!
Bounded expression-typing bridges for operator operands.  Selected named
operators attach argument coercions to already recorded operand nodes, so
their recursive boundary uses requirement retention rather than a false
whole-node-table prefix claim.  Ordinary and trait operators retain the
existing prefix-based child boundary.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

private theorem operatorRecord_nodesPrefix
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId}
    {expected : Option Ty}
    {initial : Frontend.SourceInference.State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.recordExpressionWithExpected inferenceContext source id
      type form requirements expected initial localSchemeInstantiationStart =
        .ok result) :
    initial.nodes <+: result.2.nodes := by
  obtain ⟨fitted, fittedSuccess, _, resultStateEq⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  have fittedPrefix : initial.nodes <+: fitted.state.nodes := by
    rw [(Detail.withExpected_occurrenceState_eq fittedSuccess).1]
    exact List.prefix_rfl
  rw [resultStateEq]
  exact fittedPrefix.trans
    (Frontend.SourceInference.State.recordNode_nodesPrefix fitted.state _)

/-- For an ordinary or trait unary operator, the actual operand is an
append-only recursive child of the enclosing expression.  Selected named
operators use the separate retention-aware boundary below. -/
def ordinaryUnary_childProvenance
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expression operand : Syntax.Expr}
    {operator : Syntax.Located Syntax.UnaryOp}
    {expected : Option Ty}
    {initial allocated operandState evidenceState :
      Frontend.SourceInference.State}
    {id : ExpressionId} {operandResult : InferredExpression}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {integerLiterals : List IntegerLiteralOrigin}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (parentSuccess : Detail.inferExprFuel (fuel + 1) inferenceContext
      expression expected initial = .ok result)
    (operandSuccess : Detail.inferExprFuel fuel inferenceContext operand none
      allocated = .ok (operandResult, operandState))
    (operatorSuccess : Detail.inferUnaryOperator inferenceContext
      operator.value operandResult.type expected integerLiterals operandState =
        .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type (.unary operator.value operandResult.id)
      inferred.requirements expected inferred.state = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (operandIntegerSubset :
      operandState.integerLiterals ⊆ result.2.integerLiterals)
    (parentIntegerSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements) :
    ExpressionChildInferenceProvenance (fuel + 1) inferenceContext
      (evidenceState.toTypedSource roots) evidenceState roots := by
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have below :=
      State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial
        initialBelow
    have allocatedEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [allocatedEq] using below
  have allocatedOwner : allocated.owner = initial.owner := by
    have allocatedEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← allocatedEq]
    rfl
  have operandOwner : operandState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner operandSuccess
  have parentOwner : result.2.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner parentSuccess
  have operandToParent : TypingSourceExtends
      (operandState.toTypedSource roots) (result.2.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans (allocatedOwner.symm.trans operandOwner.symm)
    · have operatorNodes :=
        (Detail.inferUnaryOperator_occurrenceState_eq operatorSuccess).1
      change operandState.nodes <+: result.2.nodes
      rw [← operatorNodes]
      exact operatorRecord_nodesPrefix recordSuccess
  have operandRequirementsSubset : operandState.requirements ⊆
      evidenceState.requirements :=
    List.Subset.trans
      (List.Subset.trans
        (Detail.inferUnaryOperator_requirements_subset operatorSuccess)
        (Detail.recordExpressionWithExpected_requirements_subset
          recordSuccess)) parentRequirementsSubset
  exact {
    fuel
    expression := operand
    expected := none
    initial := allocated
    final := operandState
    inferred := operandResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := allocatedBelow
    success := operandSuccess
    sourceExtension := TypingSourceExtends.trans operandToParent
      parentExtension
    integerLiteralsSubset := List.Subset.trans operandIntegerSubset
      parentIntegerSubset
    requirementsSubset := operandRequirementsSubset
  }

/-- In a recorded binary operator, both actual operand traces are append-only
children of the parent result.  The left source first extends through the
right traversal; the operator inference and recording tail then preserve the
completed right node table. -/
def ordinaryBinary_childProvenances
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expression left right : Syntax.Expr}
    {operator : Syntax.Located Syntax.BinaryOp}
    {expected : Option Ty}
    {initial allocated leftState rightState evidenceState :
      Frontend.SourceInference.State}
    {id : ExpressionId}
    {leftResult rightResult : InferredExpression}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {integerLiterals : List IntegerLiteralOrigin}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (parentSuccess : Detail.inferExprFuel (fuel + 1) inferenceContext
      expression expected initial = .ok result)
    (leftSuccess : Detail.inferExprFuel fuel inferenceContext left none
      allocated = .ok (leftResult, leftState))
    (rightSuccess : Detail.inferExprFuel fuel inferenceContext right none
      leftState = .ok (rightResult, rightState))
    (operatorSuccess : Detail.inferBinaryOperator inferenceContext
      operator.value leftResult.type rightResult.type expected integerLiterals
      rightState = .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type
      (.binary leftResult.id operator.value rightResult.id)
      inferred.requirements expected inferred.state = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (rightIntegerSubset :
      rightState.integerLiterals ⊆ result.2.integerLiterals)
    (parentIntegerSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements) :
    ExpressionChildInferenceProvenance (fuel + 1) inferenceContext
        (evidenceState.toTypedSource roots) evidenceState roots ×
      ExpressionChildInferenceProvenance (fuel + 1) inferenceContext
        (evidenceState.toTypedSource roots) evidenceState roots := by
  have allocatedBelow : allocated.NodesBelowNextOccurrence := by
    have below :=
      State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial
        initialBelow
    have allocatedEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [allocatedEq] using below
  have leftBelow : leftState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends leftSuccess
      ).nodesBelowNextOccurrence allocatedBelow
  have leftToRight : TypingSourceExtends
      (leftState.toTypedSource roots) (rightState.toTypedSource roots) := by
    constructor
    · exact Detail.inferExprFuel_preserves_owner rightSuccess
    · change leftState.nodes <+: rightState.nodes
      exact Detail.inferExprFuel_preserves_nodesPrefix rightSuccess
        List.prefix_rfl leftBelow (Nat.le_refl _)
  have allocatedOwner : allocated.owner = initial.owner := by
    have allocatedEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← allocatedEq]
    rfl
  have leftOwner : leftState.owner = allocated.owner :=
    Detail.inferExprFuel_preserves_owner leftSuccess
  have rightOwner : rightState.owner = leftState.owner :=
    Detail.inferExprFuel_preserves_owner rightSuccess
  have parentOwner : result.2.owner = initial.owner :=
    Detail.inferExprFuel_preserves_owner parentSuccess
  have rightToParent : TypingSourceExtends
      (rightState.toTypedSource roots) (result.2.toTypedSource roots) := by
    constructor
    · exact parentOwner.trans
        (allocatedOwner.symm.trans (leftOwner.symm.trans rightOwner.symm))
    · have operatorNodes :=
        (Detail.inferBinaryOperator_occurrenceState_eq operatorSuccess).1
      change rightState.nodes <+: result.2.nodes
      rw [← operatorNodes]
      exact operatorRecord_nodesPrefix recordSuccess
  have rightToEvidence : TypingSourceExtends
      (rightState.toTypedSource roots) (evidenceState.toTypedSource roots) :=
    TypingSourceExtends.trans rightToParent parentExtension
  have rightRequirementsSubset : rightState.requirements ⊆
      evidenceState.requirements :=
    List.Subset.trans
      (List.Subset.trans
        (Detail.inferBinaryOperator_requirements_subset operatorSuccess)
        (Detail.recordExpressionWithExpected_requirements_subset
          recordSuccess)) parentRequirementsSubset
  have rightIntegerEvidence : rightState.integerLiterals ⊆
      evidenceState.integerLiterals :=
    List.Subset.trans rightIntegerSubset parentIntegerSubset
  have leftRequirementsSubset : leftState.requirements ⊆
      evidenceState.requirements :=
    List.Subset.trans (Detail.inferExprFuel_requirements_subset rightSuccess)
      rightRequirementsSubset
  have leftIntegerEvidence : leftState.integerLiterals ⊆
      evidenceState.integerLiterals :=
    List.Subset.trans (Detail.inferExprFuel_integerLiterals_subset rightSuccess)
      rightIntegerEvidence
  exact ({
    fuel
    expression := left
    expected := none
    initial := allocated
    final := leftState
    inferred := leftResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := allocatedBelow
    success := leftSuccess
    sourceExtension := TypingSourceExtends.trans leftToRight rightToEvidence
    integerLiteralsSubset := leftIntegerEvidence
    requirementsSubset := leftRequirementsSubset
  }, {
    fuel
    expression := right
    expected := none
    initial := leftState
    final := rightState
    inferred := rightResult
    fuel_lt := Nat.lt_succ_self fuel
    initialNodesBelow := leftBelow
    success := rightSuccess
    sourceExtension := rightToEvidence
    integerLiteralsSubset := rightIntegerEvidence
    requirementsSubset := rightRequirementsSubset
  })

/-- The direct/trait unary recording tail closes against a bounded proof of
its actual operand.  The non-recursive operator certificate supplies the
operator rule; finalization supplies requirement evidence and coercion data. -/
theorem ordinaryUnary_expressionTypingBase_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty} {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat} {expression operand : Syntax.Expr}
    {operator : Syntax.Located Syntax.UnaryOp} {expected : Option Ty}
    {initial allocated operandState : Frontend.SourceInference.State}
    {id : ExpressionId} {operandResult : InferredExpression}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {integerLiterals : List IntegerLiteralOrigin}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeVarId}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (parentSuccess : Detail.inferExprFuel (fuel + 1) inferenceContext
      expression expected initial = .ok result)
    (operandSuccess : Detail.inferExprFuel fuel inferenceContext operand none
      allocated = .ok (operandResult, operandState))
    (operatorSuccess : Detail.inferUnaryOperator inferenceContext
      operator.value operandResult.type expected integerLiterals operandState =
        .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type (.unary operator.value operandResult.id)
      inferred.requirements expected inferred.state = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (operandIntegerSubset :
      operandState.integerLiterals ⊆ result.2.integerLiterals)
    (parentIntegerSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots)
      finalized.typedSource evidenceState active finalized.substitution roots)
    (operandReady : operandState.InferenceReady)
    (operandBelow : operandResult.type.VariablesBelow
      operandState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow operandState.inference.next)
    (integerLiteralsSubset :
      integerLiterals ⊆ resources.finalState.integerLiterals)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ resources.finalState.integerLiterals →
        resources.finalState.inference.substitution.apply
          (.variable origin.metavariable) = .word ∨
        resources.finalState.inference.substitution.apply
          (.variable origin.metavariable) = .integer)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (activeCatalog : SignatureCatalogWellFormed active.signatures)
    (activeBinders : TypeParameterBindersWellFormed active)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (selectedTraitName : ∀ {selectedTrait : Resolved.DeclarationId}
      {traitName : String},
      Detail.operatorTrait? inferenceContext traitName =
          .ok (some selectedTrait) →
        (inferenceContext.signatures.trait? selectedTrait).map (·.name) =
          some traitName)
    (traitSuccess : Detail.conventionalTraitWithArity? inferenceContext
      "Coerce" 2 = .ok (some trait))
    (profileSuccess : Detail.coercionMethodProfile? inferenceContext trait =
      .ok (some profile))
    (traitName : (inferenceContext.signatures.trait? trait).map (·.name) =
      some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  let child := ordinaryUnary_childProvenance allocationEq parentSuccess
    operandSuccess operatorSuccess recordSuccess initialBelow parentExtension
    operandIntegerSubset parentIntegerSubset parentRequirementsSubset
  have operandType : ExpressionHasType finalized.typedSource active
      operandResult.id (finalized.substitution.apply operandResult.type) :=
    resources.expressionHasType_of_childProvenance childSound child
      sourceBinders signaturesEq parametersEq ownerEq residual contextValid
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalRequirementsSubset : result.2.requirements ⊆
      resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact parentRequirementsSubset
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables
      sourceContext active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (inferUnaryOperator_recordExpressionWithExpected_success_expressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      operatorSuccess recordSuccess
      (by simpa only [← resources.substitution_eq] using operandType)
      operandReady operandBelow expectedBelow integerLiteralsSubset
      integerLiteralTargetsSupported finalSubstitutionExtends
      finalRequirementsSubset retained activeCatalog activeBinders
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      selectedTraitName traitName resources.solve_success
      resources.solved_context_eq resources.ledger resources.ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered)

/-- The direct/trait binary recording tail closes both actual source-ordered
operand traces against the common final source and retained operator evidence. -/
theorem ordinaryBinary_expressionTypingBase_under_ambient_bounded
    {inferenceContext : Frontend.SourceInference.Context}
    {finalType : Ty} {evidenceState : Frontend.SourceInference.State}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext finalType
      evidenceState roots finalized)
    {fuel : Nat} {expression left right : Syntax.Expr}
    {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty}
    {initial allocated leftState rightState :
      Frontend.SourceInference.State}
    {id : ExpressionId}
    {leftResult rightResult : InferredExpression}
    {inferred : Detail.OperatorInferenceResult}
    {result : InferredExpression × Frontend.SourceInference.State}
    {integerLiterals : List IntegerLiteralOrigin}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeVarId}
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (parentSuccess : Detail.inferExprFuel (fuel + 1) inferenceContext
      expression expected initial = .ok result)
    (leftSuccess : Detail.inferExprFuel fuel inferenceContext left none
      allocated = .ok (leftResult, leftState))
    (rightSuccess : Detail.inferExprFuel fuel inferenceContext right none
      leftState = .ok (rightResult, rightState))
    (operatorSuccess : Detail.inferBinaryOperator inferenceContext
      operator.value leftResult.type rightResult.type expected integerLiterals
      rightState = .ok inferred)
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id inferred.type
      (.binary leftResult.id operator.value rightResult.id)
      inferred.requirements expected inferred.state = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (parentExtension : TypingSourceExtends
      (result.2.toTypedSource roots) (evidenceState.toTypedSource roots))
    (rightIntegerSubset :
      rightState.integerLiterals ⊆ result.2.integerLiterals)
    (parentIntegerSubset :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsSubset :
      result.2.requirements ⊆ evidenceState.requirements)
    (childSound : ExpressionChildTypingCallback (fuel + 1)
      inferenceContext (evidenceState.toTypedSource roots)
      finalized.typedSource evidenceState active finalized.substitution roots)
    (rightReady : rightState.InferenceReady)
    (leftBelow : leftResult.type.VariablesBelow
      rightState.inference.next)
    (rightBelow : rightResult.type.VariablesBelow
      rightState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow rightState.inference.next)
    (integerLiteralsSubset :
      integerLiterals ⊆ resources.finalState.integerLiterals)
    (integerLiteralTargetsSupported : ∀ origin,
      origin ∈ resources.finalState.integerLiterals →
        resources.finalState.inference.substitution.apply
          (.variable origin.metavariable) = .word ∨
        resources.finalState.inference.substitution.apply
          (.variable origin.metavariable) = .integer)
    (substitutionExtends : finalized.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (activeCatalog : SignatureCatalogWellFormed active.signatures)
    (activeBinders : TypeParameterBindersWellFormed active)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (selectedTraitName : ∀ {selectedTrait : Resolved.DeclarationId}
      {traitName : String},
      Detail.operatorTrait? inferenceContext traitName =
          .ok (some selectedTrait) →
        (inferenceContext.signatures.trait? selectedTrait).map (·.name) =
          some traitName)
    (traitSuccess : Detail.conventionalTraitWithArity? inferenceContext
      "Coerce" 2 = .ok (some trait))
    (profileSuccess : Detail.coercionMethodProfile? inferenceContext trait =
      .ok (some profile))
    (traitName : (inferenceContext.signatures.trait? trait).map (·.name) =
      some "Coerce")
    (activeSignaturesEq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (activeRequirementsEq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptionsMono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution result.1 := by
  let children := ordinaryBinary_childProvenances allocationEq parentSuccess
    leftSuccess rightSuccess operatorSuccess recordSuccess initialBelow
    parentExtension rightIntegerSubset parentIntegerSubset
    parentRequirementsSubset
  have leftType : ExpressionHasType finalized.typedSource active
      leftResult.id (finalized.substitution.apply leftResult.type) :=
    resources.expressionHasType_of_childProvenance childSound children.1
      sourceBinders signaturesEq parametersEq ownerEq residual contextValid
  have rightType : ExpressionHasType finalized.typedSource active
      rightResult.id (finalized.substitution.apply rightResult.type) :=
    resources.expressionHasType_of_childProvenance childSound children.2
      sourceBinders signaturesEq parametersEq ownerEq residual contextValid
  have parentToSemantic : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource := by
    have evidenceToSemantic : TypingSourceExtends
        ((evidenceState.toTypedSource roots).applySubstitution
          finalized.substitution) finalized.typedSource := by
      rw [resources.source_eq]
      exact .refl _
    exact TypingSourceExtends.trans
      (parentExtension.applySubstitution finalized.substitution)
      evidenceToSemantic
  have retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) finalized.typedSource result.1.id :=
    ExpressionRequirementsRetainedAt.ofTypingSourceExtends
      finalized.substitution parentToSemantic
  have finalRequirementsSubset : result.2.requirements ⊆
      resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact parentRequirementsSubset
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        result.2.inference.substitution := by
    simpa only [← resources.substitution_eq] using substitutionExtends
  have finalContextValid : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables
      sourceContext active := by
    simpa only [← resources.substitution_eq] using contextValid
  simpa only [← resources.substitution_eq] using
    (inferBinaryOperator_recordExpressionWithExpected_success_expressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      operatorSuccess recordSuccess
      (by simpa only [← resources.substitution_eq] using leftType)
      (by simpa only [← resources.substitution_eq] using rightType)
      rightReady leftBelow rightBelow expectedBelow integerLiteralsSubset
      integerLiteralTargetsSupported finalSubstitutionExtends
      finalRequirementsSubset retained activeCatalog activeBinders
      traitSuccess profileSuccess catalog finalContextValid signaturesEq
      selectedTraitName traitName resources.solve_success
      resources.solved_context_eq resources.ledger resources.ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered)

/-- A selected unary operator supplies exactly one source-ordered argument
base; the callback is invoked only for the actual operand inference trace. -/
theorem selectedUnary_argumentTypingBases_of_retainedChild
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {operand : Syntax.Expr} {expected : Option Ty}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : InferredExpression} {roots : List NodeId}
    {semanticSource evidenceSource : TypedSource}
    {active : SourceSemantics.Context} {substitution : Substitution}
    (fuel_lt : fuel < parentFuel)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (success : Detail.inferExprFuel fuel inferenceContext operand expected
      initial = .ok (inferred, final))
    (integerSubset : final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (final.toTypedSource roots) evidenceSource inferred.id)
    (childSound : RetainedExpressionChildTypingCallback parentFuel
      inferenceContext (final.toTypedSource roots) semanticSource
      evidenceSource evidenceState active substitution roots) :
    ArgumentTypingBasesValid (final.toTypedSource roots) semanticSource
      active substitution [inferred] := by
  exact .cons (childSound {
    fuel
    expression := operand
    expected
    initial
    final
    inferred
    fuel_lt
    initialNodesBelow := initialBelow
    success
    sourceExtension := TypingSourceExtends.refl _
    integerLiteralsSubset := integerSubset
    requirementsSubset
  } retained) .nil

/-- Two selected binary operands are assembled in source order.  The earlier
operand base is weakened to the state at which the later operand completed;
the node-prefix premise concerns only the pre-attachment traversal. -/
theorem selectedBinary_argumentTypingBases_of_retainedChildren
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {left right : Syntax.Expr}
    {initial leftState rightState evidenceState :
      Frontend.SourceInference.State}
    {leftResult rightResult : InferredExpression}
    {roots : List NodeId}
    {semanticSource evidenceSource : TypedSource}
    {active : SourceSemantics.Context} {substitution : Substitution}
    (fuel_lt : fuel < parentFuel)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (leftSuccess : Detail.inferExprFuel fuel inferenceContext left none
      initial = .ok (leftResult, leftState))
    (leftToRight : TypingSourceExtends (leftState.toTypedSource roots)
      (rightState.toTypedSource roots))
    (rightBelow : leftState.NodesBelowNextOccurrence)
    (rightSuccess : Detail.inferExprFuel fuel inferenceContext right none
      leftState = .ok (rightResult, rightState))
    (leftIntegerSubset :
      leftState.integerLiterals ⊆ evidenceState.integerLiterals)
    (leftRequirementsSubset :
      leftState.requirements ⊆ evidenceState.requirements)
    (rightIntegerSubset :
      rightState.integerLiterals ⊆ evidenceState.integerLiterals)
    (rightRequirementsSubset :
      rightState.requirements ⊆ evidenceState.requirements)
    (leftRetained : ExpressionRequirementsRetainedAt
      (leftState.toTypedSource roots) evidenceSource leftResult.id)
    (rightRetained : ExpressionRequirementsRetainedAt
      (rightState.toTypedSource roots) evidenceSource rightResult.id)
    (childSound : RetainedExpressionChildTypingCallback parentFuel
      inferenceContext (rightState.toTypedSource roots) semanticSource
      evidenceSource evidenceState active substitution roots) :
    ArgumentTypingBasesValid (rightState.toTypedSource roots) semanticSource
      active substitution [leftResult, rightResult] := by
  have leftBase : ExpressionTypingBase (leftState.toTypedSource roots)
      semanticSource active substitution leftResult := childSound {
    fuel
    expression := left
    expected := none
    initial
    final := leftState
    inferred := leftResult
    fuel_lt
    initialNodesBelow := initialBelow
    success := leftSuccess
    sourceExtension := leftToRight
    integerLiteralsSubset := leftIntegerSubset
    requirementsSubset := leftRequirementsSubset
  } leftRetained
  have rightBase : ExpressionTypingBase (rightState.toTypedSource roots)
      semanticSource active substitution rightResult := childSound {
    fuel
    expression := right
    expected := none
    initial := leftState
    final := rightState
    inferred := rightResult
    fuel_lt
    initialNodesBelow := rightBelow
    success := rightSuccess
    sourceExtension := TypingSourceExtends.refl _
    integerLiteralsSubset := rightIntegerSubset
    requirementsSubset := rightRequirementsSubset
  } rightRetained
  exact .cons (leftBase.weakenNodeSource leftToRight.nodes_prefix)
    (.cons rightBase .nil)

end Solcore.SourceSemantics.SourceInferenceSoundness
