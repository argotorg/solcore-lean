import Solcore.SourceSemantics.SourceInferenceExpressionCallDispatchSoundness

/-!
Expression-inference bridges whose inferred root may later be rewritten by
an enclosing delayed-coercion attachment.  These theorems use
occurrence-scoped requirement retention rather than a whole-source extension
from the branch result to the final evidence source.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

/-- Numeric-literal soundness when an enclosing selected call or operator may
append coercions to the literal root.  The literal's original requirement is
transported by occurrence retention; finalization still supplies its target
support and solved evidence. -/
theorem inferExprFuel_success_numericLiteral_expressionTypingBase_scoped_of_retained
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    (resources : FinalInferenceResources inferenceContext type state roots
      finalized)
    {fuel : Nat} {expression : Syntax.Expr}
    {literal : Syntax.CoreLiteral} {source : Syntax.CoreLiteralValue}
    {rawValue : Nat} {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {inferred : InferredExpression × Frontend.SourceInference.State}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {sourceContext active : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (expression_eq : expression.value = .literal literal)
    (literal_eq : literal.value = source)
    (decoded : Frontend.numericLiteralValue? source = some rawValue)
    (allocation_eq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok inferred)
    (substitution_extends :
      finalized.substitution.SemanticallyExtends
        inferred.2.inference.substitution)
    (requirements_subset : inferred.2.requirements ⊆ state.requirements)
    (integer_literals_subset :
      inferred.2.integerLiterals ⊆ state.integerLiterals)
    (retained : ExpressionRequirementsRetainedAt
      (inferred.2.toTypedSource roots) finalized.typedSource inferred.1.id)
    (active_binders : TypeParameterBindersWellFormed active)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (context_valid : FlexibleSubstitution.ContextSubstitutionValid
      finalized.substitution closedVariables sourceContext active)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_success :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (active_signatures_eq : active.signatures =
      (finalizedRequirementContext inferenceContext finalized).signatures)
    (active_requirements_eq : active.solvedRequirements =
      (finalizedRequirementContext inferenceContext finalized
        ).solvedRequirements)
    (assumptions_mono :
      (finalizedRequirementContext inferenceContext finalized).assumptions ⊆
        active.assumptions)
    (covered : TemplateScopeCovered finalized.typedSource active
      (.expression inferred.1.id)) :
    ExpressionTypingBase (inferred.2.toTypedSource roots)
      finalized.typedSource active finalized.substitution inferred.1 := by
  let rawType := allocated.fresh.1
  let freshState := allocated.fresh.2
  let addition := freshState.addRequirementWithId
    (ProgramSignatures.builtinIntPredicate rawType)
  let origin : IntegerLiteralOrigin := {
    metavariable := ⟨allocated.inference.next⟩
    expression := id
    requirement := addition.1
  }
  let literalState : Frontend.SourceInference.State := {
    addition.2 with
    integerLiterals := addition.2.integerLiterals ++ [origin]
  }
  let resolution : IntegerLiteralResolution := {
    rawValue
    targetType := rawType
    requirement := addition.1
  }
  obtain ⟨recorded, originMember, requirementMember⟩ :=
    Detail.inferExprFuel_success_numericLiteral_record expression_eq literal_eq
      decoded allocation_eq success
  have originMemberFinal : origin ∈ state.integerLiterals :=
    integer_literals_subset originMember
  have requirementMemberFinal :
      ({ id := origin.requirement,
          predicate := ProgramSignatures.builtinIntPredicate
            (.variable origin.metavariable) } : Requirement) ∈
        state.requirements := by
    apply requirements_subset
    simpa [origin, addition, freshState, rawType,
      Frontend.SourceInference.State.fresh, TypeSystem.InferState.fresh] using
        requirementMember
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recorded roots
  have occurs : PrimaryRequirementOccursAt finalized.typedSource
      (.expression inferred.1.id) resolution.requirement := by
    apply retained recordedContains
    change resolution.requirement ∈
      [addition.1] ++ Detail.coercionRequirements coercions
    simp [resolution]
  have literalValid : IntegerLiteralValid active source
      (resolution.applySubstitution finalized.substitution) := by
    apply resources.integerLiteralValidAt
      (origin := origin) (decoded := by simpa [resolution] using decoded)
    · simp [resolution, origin, rawType,
        Frontend.SourceInference.State.fresh, TypeSystem.InferState.fresh]
    · rfl
    · exact originMemberFinal
    · exact requirementMemberFinal
    · exact active_signatures_eq
    · exact active_requirements_eq
    · exact assumptions_mono
    · exact covered
    · exact occurs
  have formType : ExpressionFormHasRawType finalized.typedSource active
      ((ExpressionForm.integerLiteral source resolution).applySubstitution
        finalized.substitution)
      (finalized.substitution.apply rawType) (.ordinary [addition.1]) := by
    simpa [ExpressionForm.applySubstitution, resolution,
      IntegerLiteralResolution.applySubstitution] using
        (ExpressionFormHasRawType.integerLiteral literalValid)
  have rawAdmissible : TypeAdmissible active
      (finalized.substitution.apply rawType) := by
    simpa [resolution, IntegerLiteralResolution.applySubstitution] using
      literalValid.target_type_admissible active_binders
  have finalSubstitutionEq :
      resources.finalState.inference.substitution = finalized.substitution :=
    resources.substitution_eq.symm
  have finalSubstitutionExtends :
      resources.finalState.inference.substitution.SemanticallyExtends
        inferred.2.inference.substitution := by
    simpa only [finalSubstitutionEq] using substitution_extends
  have requirementsSubsetFinal :
      inferred.2.requirements ⊆ resources.finalState.requirements := by
    intro requirement member
    rw [resources.requirements_eq]
    exact requirements_subset member
  have contextValidFinal : FlexibleSubstitution.ContextSubstitutionValid
      resources.finalState.inference.substitution closedVariables sourceContext
        active := by
    simpa only [finalSubstitutionEq] using context_valid
  simpa only [finalSubstitutionEq] using
    (recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
      (later := resources.finalState)
      (base := finalizedRequirementContext inferenceContext finalized)
      recorded finalSubstitutionExtends requirementsSubsetFinal retained
      (by simpa only [finalSubstitutionEq] using formType)
      (by simpa only [finalSubstitutionEq] using rawAdmissible)
      trait_success profile_success catalog contextValidFinal signatures_eq
      trait_name resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership active_signatures_eq
      active_requirements_eq assumptions_mono covered)

/-- A uniquely resolved declaration identifier remains sound when an
enclosing coercion attachment rewrites its recorded root.  Declaration
instantiation and requirement solving use the eventual evidence source;
raw-form typing may live in an independently supplied semantic source. -/
theorem inferExprFuel_success_declarationIdentifier_expressionTypingBase_scoped_of_retained
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial allocated later : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {signature : ProgramFunctionSignature}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (notBoolean :
      (name.value == "true" || name.value == "false") = false)
    (functionsEq : Detail.functionsNamed inferenceContext name.value =
      .ok [signature])
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
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
  let instantiated :=
    signature.scheme.instantiate allocated.inference.next
  let inference := {
    allocated.inference with next := instantiated.next
  }
  let advanced : Frontend.SourceInference.State := {
    allocated with inference
  }
  let allocation :=
    advanced.addRequirementsWithIds instantiated.predicates
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id instantiated.body
      (.reference name.value (.declaration
        (Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
          signature instantiated)))
      allocation.1 expected allocation.2 = .ok result := by
    simpa only [instantiated, inference, advanced, allocation] using
      (Detail.inferExprFuel_success_declarationIdentifier_record expressionEq
        allocationEq lookupEq notBoolean functionsEq success)
  have inferenceSignatureMember :
      signature ∈ inferenceContext.signatures.functions :=
    Detail.functionsNamed_success_subset_catalog functionsEq (by simp)
  have signatureMember : signature ∈ sourceContext.signatures.functions := by
    rw [signaturesEq]
    exact inferenceSignatureMember
  have instantiationValid :
      SourceSemantics.DeclarationInstantiation.Admissible sourceContext
        (Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
          signature instantiated) := by
    simpa only [instantiated] using
      (DeclarationInstantiation.ofInstantiated_admissible catalog binders
        residual signatureMember allocated.inference.next)
  have mappedInstantiationValid :
      SourceSemantics.DeclarationInstantiation.Admissible active
        ((Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
          signature instantiated).applySubstitution
            later.inference.substitution) :=
    FlexibleSubstitution.DeclarationInstantiation.Admissible.applySubstitution
      catalog contextValid instantiationValid
  have allocationAtLater : allocation.2.requirements ⊆ later.requirements :=
    List.Subset.trans
      (Detail.recordExpressionWithExpected_requirements_subset recorded)
      requirementsSubset
  have allocationCorresponds : RequirementPredicatesCorrespond
      allocation.2.requirements instantiated.predicates allocation.1 := by
    simpa only [allocation] using
      Frontend.SourceInference.State.addRequirementsWithIds_correspond
        advanced instantiated.predicates
  have laterCorresponds : RequirementPredicatesCorrespond later.requirements
      instantiated.predicates allocation.1 :=
    allocationCorresponds.mono allocationAtLater
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recorded roots
  have occurs : ∀ requirement, requirement ∈ allocation.1 →
      PrimaryRequirementOccursAt evidenceSource (.expression result.1.id)
        requirement := by
    intro requirement member
    apply retained recordedContains
    change requirement ∈
      allocation.1 ++ Detail.coercionRequirements coercions
    exact List.mem_append_left _ member
  have sequence := solveRequirements_correspondingSequenceProvesAt
    laterCorresponds solveSuccess solvedEq ledger ownership
    activeSignaturesEq activeRequirementsEq assumptionsMono covered occurs
  have predicateMapEq :
      instantiated.predicates.map (Detail.applyPredicate later) =
        instantiated.predicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution) := by
    apply List.map_congr_left
    intro predicate _
    rfl
  have finalSequence : RequirementSequenceProves active allocation.1
      (instantiated.predicates.map
        (TypedTraitResolution.applySubstitution
          later.inference.substitution)) := by
    rw [predicateMapEq] at sequence
    exact sequence
  have referenceValid : ReferenceUseValid active
      ((ReferenceResolution.declaration
        (Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
          signature instantiated)).applySubstitution
            later.inference.substitution)
      (later.inference.substitution.apply instantiated.body) allocation.1 :=
    .declaration mappedInstantiationValid finalSequence
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value (ReferenceResolution.declaration
        (Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
          signature instantiated))).applySubstitution
            later.inference.substitution)
      (later.inference.substitution.apply instantiated.body)
      (.ordinary allocation.1) :=
    .reference referenceValid
  have sourceRawAdmissible : TypeAdmissible sourceContext
      (Frontend.SourceInference.DeclarationInstantiation.ofInstantiated
        signature instantiated).type :=
    instantiationValid.type_admissible catalog binders
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply instantiated.body) := by
    simpa only
      [Frontend.SourceInference.DeclarationInstantiation.ofInstantiated] using
        (FlexibleSubstitution.TypeAdmissible.applySubstitution
          contextValid.closes sourceRawAdmissible)
  exact
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
      recorded substitutionExtends requirementsSubset retained formType
      rawAdmissible traitSuccess profileSuccess catalog contextValid
      signaturesEq traitName solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered

/-- A builtin-function identifier owns no primary declaration requirement,
so only the fitted output path needs the retained root and final ledger. -/
theorem inferExprFuel_success_builtinFunctionIdentifier_expressionTypingBase_scoped_of_retained
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial allocated later : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {function : BuiltinFunctionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (notBoolean :
      (name.value == "true" || name.value == "false") = false)
    (functionsEq : Detail.functionsNamed inferenceContext name.value = .ok [])
    (builtinEq : Frontend.builtinFunctionNamed? name.value = some function)
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (substitutionExtends :
      later.inference.substitution.SemanticallyExtends
        result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
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
  have recorded : Detail.recordExpressionWithExpected inferenceContext
      expression id function.type
      (.reference name.value (.builtinFunction function)) [] expected
      allocated = .ok result :=
    Detail.inferExprFuel_success_builtinFunctionIdentifier_record expressionEq
      allocationEq lookupEq notBoolean functionsEq builtinEq success
  have sourceReferenceValid : ReferenceUseValid sourceContext
      (.builtinFunction function) function.type [] :=
    .builtinFunction function
  have mappedReferenceValid : ReferenceUseValid active
      ((ReferenceResolution.builtinFunction function).applySubstitution
        later.inference.substitution)
      (later.inference.substitution.apply function.type) [] :=
    FlexibleSubstitution.ReferenceUseValid.applySubstitution catalog
      contextValid sourceReferenceValid
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.reference name.value
        (.builtinFunction function)).applySubstitution
          later.inference.substitution)
      (later.inference.substitution.apply function.type) (.ordinary []) :=
    .reference mappedReferenceValid
  have sourceRawAdmissible : TypeAdmissible sourceContext function.type :=
    TypeAdmissible.builtinFunction binders function
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply function.type) :=
    FlexibleSubstitution.TypeAdmissible.applySubstitution contextValid.closes
      sourceRawAdmissible
  exact
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
      recorded substitutionExtends requirementsSubset retained formType
      rawAdmissible traitSuccess profileSuccess catalog contextValid
      signaturesEq traitName solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered

/-- The selected-unary operand is a singleton argument spine.  Its recursive
proof is requested only for the successful operand trace, together with the
retention and coverage facts established for that exact occurrence after the
selected candidate attaches delayed coercions. -/
theorem selectedUnary_argumentTypingBasesValid_under_covered_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {operand : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : InferredExpression} {roots : List NodeId}
    {semanticSource evidenceSource : TypedSource}
    {active : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    (fuel_lt : fuel < parentFuel)
    (initialReady : initial.InferenceReady)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (initialInvariant : ActiveLocalContextInvariant initial substitution active)
    (initialBindersBelow : initial.LocalBindersBelowNextLocal)
    (success : Detail.inferExprFuel fuel inferenceContext operand expected
      initial = .ok (inferred, final))
    (integerSubset : final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset :
      final.requirements ⊆ evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (final.toTypedSource roots) evidenceSource inferred.id)
    (childrenRetained : ExpressionDirectChildrenRetainedAt
      (final.toTypedSource roots) evidenceSource inferred.id)
    (covered : TemplateScopeCovered evidenceSource active
      (.expression inferred.id))
    (childSound : CoveredRetainedExpressionChildTypingCallback parentFuel
      inferenceContext (final.toTypedSource roots) semanticSource
      evidenceSource evidenceState active substitution roots) :
    ArgumentTypingBasesValid (final.toTypedSource roots) semanticSource active
      substitution [inferred] := by
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
  } initialReady expectedBelow initialInvariant initialBindersBelow retained
    childrenRetained covered) .nil

/-- The selected-binary operands form a source-ordered two-element argument
spine.  The left base is weakened only through the ordinary pre-attachment
right traversal; both recursive requests then use occurrence retention and
coverage for the actual operand roots in the eventual evidence source. -/
theorem selectedBinary_argumentTypingBasesValid_under_covered_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {left right : Syntax.Expr}
    {initial leftState rightState evidenceState :
      Frontend.SourceInference.State}
    {leftResult rightResult : InferredExpression}
    {roots : List NodeId}
    {semanticSource evidenceSource : TypedSource}
    {active : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    (fuel_lt : fuel < parentFuel)
    (leftInitialReady : initial.InferenceReady)
    (leftInitialInvariant : ActiveLocalContextInvariant initial substitution
      active)
    (leftInitialBindersBelow : initial.LocalBindersBelowNextLocal)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (leftSuccess : Detail.inferExprFuel fuel inferenceContext left none
      initial = .ok (leftResult, leftState))
    (leftToRight : TypingSourceExtends (leftState.toTypedSource roots)
      (rightState.toTypedSource roots))
    (rightBelow : leftState.NodesBelowNextOccurrence)
    (rightInitialReady : leftState.InferenceReady)
    (rightInitialInvariant : ActiveLocalContextInvariant leftState substitution
      active)
    (rightInitialBindersBelow : leftState.LocalBindersBelowNextLocal)
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
    (leftChildrenRetained : ExpressionDirectChildrenRetainedAt
      (leftState.toTypedSource roots) evidenceSource leftResult.id)
    (rightChildrenRetained : ExpressionDirectChildrenRetainedAt
      (rightState.toTypedSource roots) evidenceSource rightResult.id)
    (leftCovered : TemplateScopeCovered evidenceSource active
      (.expression leftResult.id))
    (rightCovered : TemplateScopeCovered evidenceSource active
      (.expression rightResult.id))
    (childSound : CoveredRetainedExpressionChildTypingCallback parentFuel
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
  } leftInitialReady (by
      intro expectedType member
      simp at member)
    leftInitialInvariant leftInitialBindersBelow leftRetained
    leftChildrenRetained leftCovered
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
  } rightInitialReady (by
      intro expectedType member
      simp at member)
    rightInitialInvariant rightInitialBindersBelow rightRetained
    rightChildrenRetained rightCovered
  exact .cons (leftBase.weakenNodeSource leftToRight.nodes_prefix)
    (.cons rightBase .nil)

/-- The selected named-unary tail, from its actual operand inference through
candidate selection and selected-call recording.  The candidate's attachment
row proves both retention and coverage for the singleton operand before the
shared selected-call semantic core is invoked. -/
theorem
    inferExprFuel_selectFunctionCandidateFrom_recordSelectedCall_success_selectedUnary_expressionTypingBase_under_covered_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {operandSource source callee : Syntax.Expr}
    {name : String} {candidates : List ProgramFunctionSignature}
    {expected : Option TypeSystem.Ty}
    {initial operandState evidenceState : Frontend.SourceInference.State}
    {operand : InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {attempt : Detail.CandidateAttemptResult}
    {result : InferredExpression} {resultState later :
      Frontend.SourceInference.State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (operandSuccess : Detail.inferExprFuel fuel inferenceContext operandSource
      none initial = .ok (operand, operandState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext
      name candidates [operand] integerLiteralOrigins call expected
      operandState = .ok attempt)
    (recordEq : Detail.recordSelectedCall source callee name [operand] attempt =
      (result, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions)
    (initialReady : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (initialInvariant : ActiveLocalContextInvariant initial
      later.inference.substitution active)
    (initialBindersBelow : initial.LocalBindersBelowNextLocal)
    (operandIntegerSubset :
      operandState.integerLiterals ⊆ evidenceState.integerLiterals)
    (operandRequirementsSubset :
      operandState.requirements ⊆ evidenceState.requirements)
    (childSound : CoveredRetainedExpressionChildTypingCallback parentFuel
      inferenceContext (operandState.toTypedSource roots) semanticSource
      evidenceSource evidenceState active later.inference.substitution roots)
    (substitutionExtends : later.inference.substitution.SemanticallyExtends
      resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (semanticArgumentNodesPreserved : ExpressionNodesPreservedAt
      [operand.id]
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      semanticSource)
    (semanticCalleeNodePreserved : ExpressionNodesPreservedAt
      [((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).allocateExpressionId.1)]
      ((resultState.toTypedSource roots).applySubstitution
        later.inference.substitution)
      semanticSource)
    (evidenceArgumentNodesPreserved : ExpressionNodesPreservedAt
      [operand.id]
      ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      evidenceSource)
    (callRequirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered evidenceSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  have operandProperties := Detail.inferExprFuel_inferenceProperties
    initialReady signatureFormation functionsCanonical (by simp)
      operandSuccess
  have expectedAtOperand : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow operandState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      operandProperties.1.next_le
  obtain ⟨_, _, _, canonical, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation
      functionsCanonical signaturesEq candidatesSubset selectionSuccess
  have argumentExpressionIds :
      attempt.argumentCoercions.map (·.expression) = [operand.id] :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids
      canonical candidateSuccess
  have argumentIdsUnique : ([operand.id] : List ExpressionId).Nodup := by simp
  have retainedAtAttempt :=
    argumentRequirementsRetainedAt_attachExpressionCoercions_of_ids
      (state := attempt.state) (roots := roots)
      (evidenceSource := evidenceSource)
      (substitution := later.inference.substitution)
      (arguments := [operand]) (entries := attempt.argumentCoercions)
      argumentExpressionIds argumentIdsUnique
      (by
        intro expressionId node member contains
        apply evidenceArgumentNodesPreserved
        · simpa using member
        · exact contains)
  have candidateNodesEq : attempt.state.nodes = operandState.nodes :=
    (Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1
  have operandRetained : ExpressionRequirementsRetainedAt
      (operandState.toTypedSource roots) evidenceSource operand.id := by
    intro node requirement contains requirementMember
    apply retainedAtAttempt operand (by simp)
    · rcases contains with ⟨member, idEq⟩
      refine ⟨?_, idEq⟩
      change Node.expression node ∈ attempt.state.nodes
      rw [candidateNodesEq]
      exact member
    · exact requirementMember
  have operandChildrenRetained : ExpressionDirectChildrenRetainedAt
      (operandState.toTypedSource roots) evidenceSource operand.id := by
    have operandToAttempt : ExpressionDirectChildrenRetainedAt
        (operandState.toTypedSource roots) (attempt.state.toTypedSource roots)
        operand.id := by
      apply ExpressionDirectChildrenRetainedAt.ofNodesEq
      exact candidateNodesEq
    have attemptToAttached : ExpressionDirectChildrenRetainedAt
        (attempt.state.toTypedSource roots)
        ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).toTypedSource roots) operand.id :=
      ExpressionDirectChildrenRetainedAt.ofAttachExpressionCoercions
        attempt.state attempt.argumentCoercions roots operand.id
    have attachedToEvidence : ExpressionDirectChildrenRetainedAt
        ((Detail.attachExpressionCoercions attempt.state
          attempt.argumentCoercions).toTypedSource roots)
        evidenceSource operand.id :=
      ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt
        (substitution := later.inference.substitution)
        evidenceArgumentNodesPreserved
    intro child edge
    exact attachedToEvidence (attemptToAttached (operandToAttempt edge))
  have operandCovered : TemplateScopeCovered evidenceSource active
      (.expression operand.id) := by
    have operandIdMember : operand.id ∈
        attempt.argumentCoercions.map (·.expression) := by
      rw [argumentExpressionIds]
      simp
    obtain ⟨entry, entryMember, entryIdEq⟩ :=
      List.mem_map.mp operandIdMember
    simpa only [entryIdEq] using argumentCovered entry entryMember
  have bases :=
    selectedUnary_argumentTypingBasesValid_under_covered_retained_bounded
      fuel_lt initialReady (by
        intro expectedType member
        simp at member)
      initialBelow initialInvariant initialBindersBelow operandSuccess
      operandIntegerSubset
      operandRequirementsSubset operandRetained operandChildrenRetained
      operandCovered childSound
  exact
    selectFunctionCandidateFrom_recordSelectedCall_success_expressionTypingBase_scoped_of_retained
      selectionSuccess recordEq candidatesSubset bases argumentIdsUnique
      operandProperties.2.1 (by simpa using operandProperties.2.2)
      signatureFormation functionsCanonical expectedAtOperand
      substitutionExtends requirementsSubset semanticArgumentNodesPreserved
      semanticCalleeNodePreserved evidenceArgumentNodesPreserved
      callRequirementsRetained argumentCovered catalog binders residual
      contextValid signaturesEq traitSuccess profileSuccess traitName
      solveSuccess solvedEq ledger ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono callCovered

/-- The selected named-binary tail.  Binary selection first fixes a Boolean
candidate result and then fits that result to the enclosing expectation.  This
bridge composes the actual candidate, fitting, and recording progress, proves
the trailing fitted coercion path from the retained call-root requirements,
and supplies the shared selected-call core with bases for exactly the two
successful operand traces. -/
theorem
    inferExprFuel_selectFunctionCandidateFrom_withExpected_recordSelectedCallResult_success_selectedBinary_expressionTypingBase_under_covered_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {leftSource rightSource source callee : Syntax.Expr}
    {name : String} {candidates : List ProgramFunctionSignature}
    {expected : Option TypeSystem.Ty}
    {initial leftState rightState evidenceState :
      Frontend.SourceInference.State}
    {left right : InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {attempt : Detail.CandidateAttemptResult}
    {fitted : Detail.ExpectationResult}
    {result : InferredExpression} {resultState later :
      Frontend.SourceInference.State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (leftSuccess : Detail.inferExprFuel fuel inferenceContext leftSource none
      initial = .ok (left, leftState))
    (rightSuccess : Detail.inferExprFuel fuel inferenceContext rightSource none
      leftState = .ok (right, rightState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext
      name candidates [left, right] integerLiteralOrigins call (some .bool)
      rightState = .ok attempt)
    (fittingSuccess : Detail.withExpected inferenceContext attempt.state
      attempt.result expected = .ok fitted)
    (recordEq : Detail.recordSelectedCallResult source callee name
      [left, right] attempt fitted.expression fitted.coercions fitted.state =
        (result, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions)
    (initialReady : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (initialInvariant : ActiveLocalContextInvariant initial
      later.inference.substitution active)
    (initialBindersBelow : initial.LocalBindersBelowNextLocal)
    (rightIntegerSubset :
      rightState.integerLiterals ⊆ evidenceState.integerLiterals)
    (rightRequirementsEvidenceSubset :
      rightState.requirements ⊆ evidenceState.requirements)
    (childSound : CoveredRetainedExpressionChildTypingCallback parentFuel
      inferenceContext (rightState.toTypedSource roots) semanticSource
      evidenceSource evidenceState active later.inference.substitution roots)
    (substitutionExtends : later.inference.substitution.SemanticallyExtends
      resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (semanticArgumentNodesPreserved : ExpressionNodesPreservedAt
      [left.id, right.id]
      ((Detail.attachExpressionCoercions fitted.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      semanticSource)
    (semanticCalleeNodePreserved : ExpressionNodesPreservedAt
      [((Detail.attachExpressionCoercions fitted.state
          attempt.argumentCoercions).allocateExpressionId.1)]
      ((resultState.toTypedSource roots).applySubstitution
        later.inference.substitution)
      semanticSource)
    (evidenceArgumentNodesPreserved : ExpressionNodesPreservedAt
      [left.id, right.id]
      ((Detail.attachExpressionCoercions fitted.state
          attempt.argumentCoercions
        |>.toTypedSource roots).applySubstitution
          later.inference.substitution)
      evidenceSource)
    (callRequirementsRetained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (argumentCovered : ∀ entry ∈ attempt.argumentCoercions,
      TemplateScopeCovered evidenceSource active
        (.expression entry.expression))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (callCovered : TemplateScopeCovered evidenceSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  have returnedEq : result = fitted.expression :=
    (Detail.recordSelectedCallResult_success_nodes recordEq).1
  subst result
  have leftProperties := Detail.inferExprFuel_inferenceProperties
    initialReady signatureFormation functionsCanonical (by simp) leftSuccess
  have leftBelow : leftState.NodesBelowNextOccurrence :=
    (Detail.inferExprFuel_occurrenceBoundExtends leftSuccess
      ).nodesBelowNextOccurrence initialBelow
  have leftInvariant : ActiveLocalContextInvariant leftState
      later.inference.substitution active :=
    initialInvariant.inferExprFuel leftSuccess
  have leftBindersBelow : leftState.LocalBindersBelowNextLocal :=
    Detail.inferExprFuel_preserves_localBindersBelowNextLocal
      initialBindersBelow leftSuccess
  have rightProperties := Detail.inferExprFuel_inferenceProperties
    leftProperties.2.1 signatureFormation functionsCanonical (by simp)
      rightSuccess
  have leftToRight : TypingSourceExtends (leftState.toTypedSource roots)
      (rightState.toTypedSource roots) :=
    inferExprFuel_success_typingSourceExtends rightSuccess leftBelow roots
  have argumentsBelow : ∀ argument ∈ [left, right],
      argument.type.VariablesBelow rightState.inference.next := by
    intro argument member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · exact leftProperties.2.2.weaken rightProperties.1.next_le
    · exact rightProperties.2.2
  have expectedAtRight : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow rightState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (leftProperties.1.trans rightProperties.1).next_le
  obtain ⟨signature, _, signatureMember, canonical, schemeBodyBelow,
      candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation
      functionsCanonical signaturesEq candidatesSubset selectionSuccess
  have candidateProperties :=
    Detail.tryFunctionCandidate_some_inferenceProperties
      rightProperties.2.1 argumentsBelow schemeBodyBelow (by
        intro candidate member
        simp only [Option.mem_def] at member
        cases member
        simp [TypeSystem.Ty.bool])
        candidateSuccess
  have expectedAtAttempt : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow attempt.state.inference.next := by
    intro expectedType member
    exact (expectedAtRight expectedType member).weaken
      candidateProperties.1.next_le
  have fittingProperties := Detail.withExpected_inferenceProperties
    candidateProperties.2.1 candidateProperties.2.2 expectedAtAttempt
      fittingSuccess
  have recordProperties :=
    Detail.recordSelectedCallResult_inferenceProperties source callee name
      [left, right] attempt fitted.expression fitted.coercions fitted.state
      fittingProperties.2.1 fittingProperties.2.2
  rw [recordEq] at recordProperties
  have laterExtendsFitted : later.inference.substitution.SemanticallyExtends
      fitted.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
      recordProperties.1.substitution_extends
  have laterExtendsAttempt : later.inference.substitution.SemanticallyExtends
      attempt.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterExtendsFitted
      fittingProperties.1.substitution_extends
  have recordRequirementsSubset : fitted.state.requirements ⊆
      resultState.requirements := by
    have subset := Detail.recordSelectedCallResult_requirements_subset source
      callee name [left, right] attempt fitted.expression fitted.coercions
      fitted.state
    rw [recordEq] at subset
    exact subset
  have fittedRequirementsSubset : fitted.state.requirements ⊆
      later.requirements :=
    List.Subset.trans recordRequirementsSubset requirementsSubset
  have candidateRequirementsSubset : attempt.state.requirements ⊆
      later.requirements :=
    List.Subset.trans
      (Detail.withExpected_requirements_subset fittingSuccess)
      fittedRequirementsSubset
  have argumentExpressionIds :
      attempt.argumentCoercions.map (·.expression) =
        [left.id, right.id] :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids
      canonical candidateSuccess
  have argumentIdsUnique :
      ([left.id, right.id] : List ExpressionId).Nodup :=
    by
      apply List.nodup_cons.mpr
      constructor
      · intro member
        have idEq : left.id = right.id := by simpa using member
        have indexEq := congrArg
          (fun expressionId : ExpressionId => expressionId.occurrence.index)
          idEq
        rw [Detail.inferExprFuel_success_id_index leftSuccess,
          Detail.inferExprFuel_success_id_index rightSuccess] at indexEq
        exact (Nat.ne_of_lt
          (Detail.inferExprFuel_nextOccurrence_lt leftSuccess)) indexEq
      · apply List.nodup_cons.mpr
        exact ⟨by simp, List.nodup_nil⟩
  have retainedAtFitted :=
    argumentRequirementsRetainedAt_attachExpressionCoercions_of_ids
      (state := fitted.state) (roots := roots)
      (evidenceSource := evidenceSource)
      (substitution := later.inference.substitution)
      (arguments := [left, right]) (entries := attempt.argumentCoercions)
      argumentExpressionIds argumentIdsUnique
      (by
        intro expressionId node member contains
        apply evidenceArgumentNodesPreserved
        · simpa using member
        · exact contains)
  have fittedNodesEq : fitted.state.nodes = attempt.state.nodes :=
    (Detail.withExpected_occurrenceState_eq fittingSuccess).1
  have candidateNodesEq : attempt.state.nodes = rightState.nodes :=
    (Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1
  have retainedAtRight : ∀ argument ∈ [left, right],
      ExpressionRequirementsRetainedAt
        (rightState.toTypedSource roots) evidenceSource argument.id := by
    intro argument argumentMember node requirement contains requirementMember
    apply retainedAtFitted argument argumentMember
    · rcases contains with ⟨member, idEq⟩
      refine ⟨?_, idEq⟩
      change Node.expression node ∈ fitted.state.nodes
      rw [fittedNodesEq, candidateNodesEq]
      exact member
    · exact requirementMember
  have childrenRetainedAtRight : ∀ argument ∈ [left, right],
      ExpressionDirectChildrenRetainedAt
        (rightState.toTypedSource roots) evidenceSource argument.id := by
    intro argument argumentMember
    have rightToAttempt : ExpressionDirectChildrenRetainedAt
        (rightState.toTypedSource roots) (attempt.state.toTypedSource roots)
        argument.id := by
      apply ExpressionDirectChildrenRetainedAt.ofNodesEq
      exact candidateNodesEq
    have attemptToFitted : ExpressionDirectChildrenRetainedAt
        (attempt.state.toTypedSource roots) (fitted.state.toTypedSource roots)
        argument.id := by
      apply ExpressionDirectChildrenRetainedAt.ofNodesEq
      exact fittedNodesEq
    have fittedToAttached : ExpressionDirectChildrenRetainedAt
        (fitted.state.toTypedSource roots)
        ((Detail.attachExpressionCoercions fitted.state
          attempt.argumentCoercions).toTypedSource roots) argument.id :=
      ExpressionDirectChildrenRetainedAt.ofAttachExpressionCoercions
        fitted.state attempt.argumentCoercions roots argument.id
    have attachedToEvidence : ExpressionDirectChildrenRetainedAt
        ((Detail.attachExpressionCoercions fitted.state
          attempt.argumentCoercions).toTypedSource roots)
        evidenceSource argument.id := by
      apply ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt
        (substitution := later.inference.substitution)
      intro expressionId node member contains
      simp only [List.mem_singleton] at member
      subst expressionId
      apply evidenceArgumentNodesPreserved
      · exact List.mem_map.mpr ⟨argument, argumentMember, rfl⟩
      · exact contains
    intro child edge
    exact attachedToEvidence
      (fittedToAttached (attemptToFitted (rightToAttempt edge)))
  have coveredArguments : ∀ argument ∈ [left, right],
      TemplateScopeCovered evidenceSource active
        (.expression argument.id) := by
    intro argument argumentMember
    have argumentIdMember : argument.id ∈ [left.id, right.id] :=
      List.mem_map.mpr ⟨argument, argumentMember, rfl⟩
    have entryIdMember : argument.id ∈
        attempt.argumentCoercions.map (·.expression) := by
      rw [argumentExpressionIds]
      exact argumentIdMember
    obtain ⟨entry, entryMember, entryIdEq⟩ :=
      List.mem_map.mp entryIdMember
    simpa only [entryIdEq] using argumentCovered entry entryMember
  have leftIntegerSubset :
      leftState.integerLiterals ⊆ evidenceState.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset rightSuccess)
      rightIntegerSubset
  have leftRequirementsSubset :
      leftState.requirements ⊆ evidenceState.requirements :=
    List.Subset.trans (Detail.inferExprFuel_requirements_subset rightSuccess)
      rightRequirementsEvidenceSubset
  have leftRetained : ExpressionRequirementsRetainedAt
      (leftState.toTypedSource roots) evidenceSource left.id :=
    ExpressionRequirementsRetainedAt.monoBefore leftToRight
      (retainedAtRight left (by simp))
  have leftChildrenRetained : ExpressionDirectChildrenRetainedAt
      (leftState.toTypedSource roots) evidenceSource left.id :=
    ExpressionDirectChildrenRetainedAt.monoBefore leftToRight
      (childrenRetainedAtRight left (by simp))
  have bases :=
    selectedBinary_argumentTypingBasesValid_under_covered_retained_bounded
      fuel_lt initialReady initialInvariant initialBindersBelow initialBelow
      leftSuccess leftToRight leftBelow leftProperties.2.1 leftInvariant
      leftBindersBelow rightSuccess
      leftIntegerSubset leftRequirementsSubset rightIntegerSubset
      rightRequirementsEvidenceSubset
      leftRetained
      (retainedAtRight right (by simp))
      leftChildrenRetained
      (childrenRetainedAtRight right (by simp))
      (coveredArguments left (by simp))
      (coveredArguments right (by simp)) childSound
  have callContains :=
    recordSelectedCallResult_success_containsExpression recordEq roots
  have trailingOccurs : ∀ requirement,
      requirement ∈ coercionRequirementIds fitted.coercions →
        PrimaryRequirementOccursAt evidenceSource
          (.expression fitted.expression.id) requirement := by
    intro requirement member
    apply callRequirementsRetained callContains
    change requirement ∈
      (Detail.coercionRequirements attempt.callCoercions ++
        attempt.signatureRequirements) ++
          Detail.coercionRequirements fitted.coercions
    apply List.mem_append_right
    simpa [Detail.coercionRequirements, coercionRequirementIds] using member
  have trailingPathRaw :=
    withExpected_success_coercionPathValid_afterFinalization_scoped
      fittingSuccess traitSuccess profileSuccess fittedRequirementsSubset
      catalog contextValid signaturesEq traitName solveSuccess solvedEq ledger
      ownership activeSignaturesEq activeRequirementsEq assumptionsMono
      callCovered trailingOccurs
  have fittedEndpointEq : later.inference.substitution.apply
      (fitted.state.resolve attempt.result.type) =
      later.inference.substitution.apply attempt.result.type :=
    TypeSystem.InferState.apply_resolve_eq_apply laterExtendsFitted _
  have trailingPath : CoercionPathValid active
      (later.inference.substitution.apply attempt.result.type)
      (later.inference.substitution.apply fitted.expression.type)
      (fitted.coercions.map
        (CoercionStep.applySubstitution later.inference.substitution)) := by
    rw [← fittedEndpointEq]
    exact trailingPathRaw
  exact
    tryFunctionCandidate_some_recordSelectedCallResult_success_expressionTypingBase_scoped_of_retained
      canonical candidateSuccess recordEq fittedNodesEq
      (Detail.withExpected_success_expression_id fittingSuccess) bases
      argumentIdsUnique rightProperties.2.1 argumentsBelow schemeBodyBelow
      (by
        intro candidate member
        simp only [Option.mem_def] at member
        cases member
        simp [TypeSystem.Ty.bool])
      laterExtendsAttempt laterExtendsFitted
      candidateRequirementsSubset semanticArgumentNodesPreserved
      semanticCalleeNodePreserved evidenceArgumentNodesPreserved
      callRequirementsRetained argumentCovered catalog binders residual
      signatureMember contextValid signaturesEq traitSuccess profileSuccess
      traitName solveSuccess solvedEq ledger ownership activeSignaturesEq
      activeRequirementsEq assumptionsMono callCovered trailingPath

/-- Constructor-argument traversal under the closed mutual boundary.  Every
recursive invocation is an actual traversal head and receives its concrete
child-to-row source link, final-ledger subsets, occurrence retention, and
scope coverage.  Exact payload preservation is required only at the argument
identities when bases are closed into ordinary expression typings. -/
theorem
    inferConstructorArgumentsFuel_success_expressionsHaveTypes_under_covered_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {sources : List Syntax.Expr} {expectedTypes : List TypeSystem.Ty}
    {initial final evidenceState : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    {roots : List NodeId}
    {semanticSource evidenceSource : TypedSource}
    {active : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    (fuel_lt : fuel < parentFuel)
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expected ∈ expectedTypes,
      expected.VariablesBelow initial.inference.next)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (initialInvariant : ActiveLocalContextInvariant initial outer active)
    (initialBindersBelow : initial.LocalBindersBelowNextLocal)
    (outerExtension : outer.SemanticallyExtends
      final.inference.substitution)
    (integerLiteralsSubset :
      final.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset : final.requirements ⊆ evidenceState.requirements)
    (retained : ∀ argument ∈ inferred,
      ExpressionRequirementsRetainedAt (final.toTypedSource roots)
        evidenceSource argument.id)
    (childrenRetained : ∀ argument ∈ inferred,
      ExpressionDirectChildrenRetainedAt (final.toTypedSource roots)
        evidenceSource argument.id)
    (covered : ∀ argument ∈ inferred,
      TemplateScopeCovered evidenceSource active (.expression argument.id))
    (preserved : ExpressionNodesPreservedAt (inferred.map (·.id))
      ((final.toTypedSource roots).applySubstitution outer) semanticSource)
    (childSound : CoveredRetainedExpressionChildTypingCallback parentFuel
      inferenceContext (final.toTypedSource roots) semanticSource
      evidenceSource evidenceState active outer roots)
    (expectedAdmissible : ∀ expected ∈ expectedTypes,
      TypeAdmissible active (outer.apply expected))
    (success : Detail.inferConstructorArgumentsFuel fuel inferenceContext
      sources expectedTypes initial = .ok (inferred, final)) :
    ExpressionsHaveTypes semanticSource active (inferred.map (·.id))
      (expectedTypes.map outer.apply) := by
  induction sources generalizing expectedTypes initial inferred final with
  | nil =>
      cases expectedTypes with
      | nil =>
          simp only [Detail.inferConstructorArgumentsFuel, pure, Pure.pure,
            Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil active
      | cons expected expectedTypes =>
          simp [Detail.inferConstructorArgumentsFuel] at success
  | cons source sources induction =>
      cases expectedTypes with
      | nil =>
          simp [Detail.inferConstructorArgumentsFuel] at success
      | cons expected expectedTypes =>
          unfold Detail.inferConstructorArgumentsFuel at success
          cases headSuccess : Detail.inferExprFuel fuel inferenceContext source
              (some (initial.resolve expected)) initial with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headPair =>
              rcases headPair with ⟨head, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferConstructorArgumentsFuel fuel
                  inferenceContext sources expectedTypes headState with
              | error error =>
                  simp [tailSuccess] at success
              | ok tailPair =>
                  rcases tailPair with ⟨tail, tailState⟩
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  cases resultEq
                  have expectedHeadBelow :
                      expected.VariablesBelow initial.inference.next :=
                    expectedBelow expected (by simp)
                  have resolvedHeadBelow :
                      (initial.resolve expected).VariablesBelow
                        initial.inference.next :=
                    ready.solved.variablesBelow_apply expectedHeadBelow
                  have headProperties :=
                    Detail.inferExprFuel_inferenceProperties ready
                      signatureFormation functionsCanonical (by
                        intro candidate member
                        simp only [Option.mem_def] at member
                        injection member with candidateEq
                        subst candidate
                        exact resolvedHeadBelow) headSuccess
                  have headBelow : headState.NodesBelowNextOccurrence :=
                    (Detail.inferExprFuel_occurrenceBoundExtends headSuccess
                      ).nodesBelowNextOccurrence initialBelow
                  have headInvariant : ActiveLocalContextInvariant headState
                      outer active :=
                    initialInvariant.inferExprFuel headSuccess
                  have headBindersBelow :
                      headState.LocalBindersBelowNextLocal :=
                    Detail.inferExprFuel_preserves_localBindersBelowNextLocal
                      initialBindersBelow headSuccess
                  have tailExpectedBelow : ∀ candidate ∈ expectedTypes,
                      candidate.VariablesBelow headState.inference.next := by
                    intro candidate member
                    exact (expectedBelow candidate (by simp [member])).weaken
                      headProperties.1.next_le
                  have tailProperties :=
                    Detail.inferConstructorArgumentsFuel_inferenceProperties
                      headProperties.2.1 signatureFormation functionsCanonical
                      tailExpectedBelow tailSuccess
                  have outerHead : outer.SemanticallyExtends
                      headState.inference.substitution :=
                    TypeSystem.Substitution.SemanticallyExtends.trans
                      outerExtension tailProperties.1.substitution_extends
                  have outerInitial : outer.SemanticallyExtends
                      initial.inference.substitution :=
                    TypeSystem.Substitution.SemanticallyExtends.trans outerHead
                      headProperties.1.substitution_extends
                  have headToFinal : TypingSourceExtends
                      (headState.toTypedSource roots)
                      (final.toTypedSource roots) :=
                    inferConstructorArgumentsFuel_success_typingSourceExtends
                      tailSuccess headBelow roots
                  have headIntegerLiteralsSubset :
                      headState.integerLiterals ⊆
                        evidenceState.integerLiterals :=
                    List.Subset.trans
                      (Detail.inferConstructorArgumentsFuel_integerLiterals_subset
                        tailSuccess)
                      integerLiteralsSubset
                  have headRequirementsSubset :
                      headState.requirements ⊆
                        evidenceState.requirements :=
                    List.Subset.trans
                      (Detail.inferConstructorArgumentsFuel_requirements_subset
                        tailSuccess)
                      requirementsSubset
                  let child : ExpressionChildInferenceProvenance parentFuel
                      inferenceContext (final.toTypedSource roots)
                      evidenceState roots := {
                    fuel
                    expression := source
                    expected := some (initial.resolve expected)
                    initial
                    final := headState
                    inferred := head
                    fuel_lt
                    initialNodesBelow := initialBelow
                    success := headSuccess
                    sourceExtension := headToFinal
                    integerLiteralsSubset := headIntegerLiteralsSubset
                    requirementsSubset := headRequirementsSubset
                  }
                  have headRetainedAtFinal : ExpressionRequirementsRetainedAt
                      (final.toTypedSource roots) evidenceSource head.id :=
                    retained head (by simp)
                  have headRetained : ExpressionRequirementsRetainedAt
                      (headState.toTypedSource roots) evidenceSource head.id :=
                    ExpressionRequirementsRetainedAt.monoBefore headToFinal
                      headRetainedAtFinal
                  have headChildrenRetainedAtFinal :
                      ExpressionDirectChildrenRetainedAt
                        (final.toTypedSource roots) evidenceSource head.id :=
                    childrenRetained head (by simp)
                  have headChildrenRetained :
                      ExpressionDirectChildrenRetainedAt
                        (headState.toTypedSource roots) evidenceSource
                        head.id :=
                    ExpressionDirectChildrenRetainedAt.monoBefore headToFinal
                      headChildrenRetainedAtFinal
                  have headCovered : TemplateScopeCovered evidenceSource active
                      (.expression head.id) :=
                    covered head (by simp)
                  have headBase := childSound child ready (by
                      intro candidate member
                      simp only [Option.mem_def] at member
                      injection member with candidateEq
                      subst candidate
                      exact resolvedHeadBelow)
                    initialInvariant initialBindersBelow headRetained
                    headChildrenRetained headCovered
                  have finalHeadBase : ExpressionTypingBase
                      (final.toTypedSource roots) semanticSource active outer
                      head :=
                    headBase.weakenNodeSource headToFinal.nodes_prefix
                  have headExpectedEq : outer.apply head.type =
                      outer.apply expected := by
                    calc
                      outer.apply head.type =
                          outer.apply (initial.resolve expected) :=
                        Detail.inferExprFuel_expected_type_apply_eq headSuccess
                          outerHead
                      _ = outer.apply expected := by
                        simpa [Frontend.SourceInference.State.resolve,
                          TypeSystem.InferState.resolve] using
                            outerInitial expected
                  have headAdmissible : TypeAdmissible active
                      (outer.apply head.type) := by
                    rw [headExpectedEq]
                    exact expectedAdmissible expected (by simp)
                  have headPreserved : ExpressionNodesPreservedAt [head.id]
                      ((final.toTypedSource roots).applySubstitution outer)
                      semanticSource := by
                    intro expressionId node member contains
                    have expressionIdEq : expressionId = head.id := by
                      simpa using member
                    subst expressionId
                    apply preserved
                    · simp
                    · exact contains
                  have headType : ExpressionHasType semanticSource active
                      head.id (outer.apply head.type) :=
                    finalHeadBase.expressionHasType headPreserved headAdmissible
                  have headExpected : ExpressionHasType semanticSource active
                      head.id (outer.apply expected) := by
                    rw [← headExpectedEq]
                    exact headType
                  have tailTyping := induction
                    headProperties.2.1 tailExpectedBelow headBelow headInvariant
                    headBindersBelow outerExtension integerLiteralsSubset
                    requirementsSubset
                    (retained := by
                      intro argument member
                      exact retained argument
                        (List.mem_cons_of_mem head member))
                    (childrenRetained := by
                      intro argument member
                      exact childrenRetained argument
                        (List.mem_cons_of_mem head member))
                    (covered := by
                      intro argument member
                      exact covered argument
                        (List.mem_cons_of_mem head member))
                    (preserved := by
                      intro expressionId node member contains
                      apply preserved
                      · exact List.mem_cons_of_mem head.id member
                      · exact contains)
                    childSound
                    (expectedAdmissible := by
                      intro candidate member
                      exact expectedAdmissible candidate
                        (List.mem_cons_of_mem expected member))
                    tailSuccess
                  exact .cons headExpected tailTyping

/-- The occurrence-scoped facts which an enclosing constructor expression
supplies for the exact argument row produced by its successful traversal. -/
structure ConstructorArgumentsFinalEvidence
    (state : Frontend.SourceInference.State)
    (arguments : List InferredExpression)
    (roots : List NodeId)
    (substitution : TypeSystem.Substitution)
    (semanticSource evidenceSource : TypedSource)
    (active : SourceSemantics.Context) : Prop where
  retained : ∀ argument ∈ arguments,
    ExpressionRequirementsRetainedAt (state.toTypedSource roots)
      evidenceSource argument.id
  childrenRetained : ∀ argument ∈ arguments,
    ExpressionDirectChildrenRetainedAt (state.toTypedSource roots)
      evidenceSource argument.id
  covered : ∀ argument ∈ arguments,
    TemplateScopeCovered evidenceSource active (.expression argument.id)
  preserved : ExpressionNodesPreservedAt (arguments.map (·.id))
    ((state.toTypedSource roots).applySubstitution substitution)
    semanticSource

/-- The nonrecursive constructor-recording tail with independent semantic and
evidence sources.  Its payload expressions are already typed in the semantic
source; the constructor root's requirements and fitted output path are
validated through occurrence retention in the evidence source. -/
theorem
    recordExpressionWithExpected_success_constructor_expressionTypingBase_scoped_of_retained
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation}
    {arguments : List InferredExpression}
    {expected : Option TypeSystem.Ty}
    {argumentState resultState later : Frontend.SourceInference.State}
    {result : InferredExpression}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      source id (argumentState.resolve instantiation.resultType)
      (.constructor instantiation (arguments.map (·.id))) [] expected
      argumentState none = .ok (result, resultState))
    (outerArguments : later.inference.substitution.SemanticallyExtends
      argumentState.inference.substitution)
    (argumentsType : ExpressionsHaveTypes semanticSource active
      (arguments.map (·.id))
      (instantiation.payloadTypes.map later.inference.substitution.apply))
    (binders : TypeParameterBindersWellFormed active)
    (instantiationValid :
      SourceSemantics.DataConstructorInstantiation.Admissible active
        (instantiation.applySubstitution later.inference.substitution))
    (substitutionExtends : later.inference.substitution.SemanticallyExtends
      resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered evidenceSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  have rawTypeEq : later.inference.substitution.apply
      (argumentState.resolve instantiation.resultType) =
      later.inference.substitution.apply instantiation.resultType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        outerArguments instantiation.resultType
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply
        (argumentState.resolve instantiation.resultType)) := by
    rw [rawTypeEq]
    simpa [DataConstructorInstantiation.applySubstitution] using
      (SourceSemantics.DataConstructorInstantiation.Admissible.result_type_admissible
        binders instantiationValid)
  have formType : ExpressionFormHasRawType semanticSource active
      ((.constructor instantiation
          (arguments.map (·.id)) : ExpressionForm).applySubstitution
        later.inference.substitution)
      (later.inference.substitution.apply
        (argumentState.resolve instantiation.resultType))
      (.ordinary []) := by
    rw [rawTypeEq]
    simpa [ExpressionForm.applySubstitution,
      DataConstructorInstantiation.applySubstitution] using
        (ExpressionFormHasRawType.constructor instantiationValid
          argumentsType)
  exact
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
      recordSuccess substitutionExtends requirementsSubset retained formType
      rawAdmissible traitSuccess profileSuccess catalog contextValid
      signaturesEq traitName solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered

/-- Constructor-application soundness across the optional expected-type
unification prefix.  The recursive boundary is instantiated only for the
argument traversal exposed by this successful constructor branch.  Exact
argument preservation, requirement retention, and scope coverage are likewise
supplied for that same traversal/recording pair, so no append-only claim is
made across a later delayed-coercion rewrite. -/
theorem
    inferConstructorApplicationFuel_success_expressionTypingBase_under_covered_retained_bounded
    {parentFuel fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial resultState later evidenceState : Frontend.SourceInference.State}
    {result : InferredExpression}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (fuel_lt : fuel < parentFuel)
    (success : Detail.inferConstructorApplicationFuel fuel inferenceContext
      source id instantiation arguments expected initial =
        .ok (result, resultState))
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (payloadBelow : ∀ payload ∈ instantiation.payloadTypes,
      payload.VariablesBelow initial.inference.next)
    (resultBelow : instantiation.resultType.VariablesBelow
      initial.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next)
    (nodesBelow : initial.NodesBelowNextOccurrence)
    (initialInvariant : ActiveLocalContextInvariant initial
      later.inference.substitution active)
    (initialBindersBelow : initial.LocalBindersBelowNextLocal)
    (substitutionExtends : later.inference.substitution.SemanticallyExtends
      resultState.inference.substitution)
    (requirementsSubset : resultState.requirements ⊆ later.requirements)
    (parentIntegerLiteralsSubset :
      resultState.integerLiterals ⊆ evidenceState.integerLiterals)
    (parentRequirementsEvidenceSubset :
      resultState.requirements ⊆ evidenceState.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (resultState.toTypedSource roots) evidenceSource result.id)
    (argumentsEvidence :
      ∀ {argumentInitial argumentsState : Frontend.SourceInference.State}
        {inferredArguments : List InferredExpression},
        Detail.inferConstructorArgumentsFuel fuel inferenceContext arguments
            instantiation.payloadTypes argumentInitial =
          .ok (inferredArguments, argumentsState) →
        Detail.recordExpressionWithExpected inferenceContext source id
            (argumentsState.resolve instantiation.resultType)
            (.constructor instantiation (inferredArguments.map (·.id))) []
            expected argumentsState none = .ok (result, resultState) →
          ConstructorArgumentsFinalEvidence argumentsState inferredArguments
            roots later.inference.substitution semanticSource evidenceSource
            active)
    (childSound : ∀ {ambient : Frontend.SourceInference.State},
      CoveredRetainedExpressionChildTypingCallback parentFuel
        inferenceContext (ambient.toTypedSource roots) semanticSource
        evidenceSource evidenceState active later.inference.substitution roots)
    (activeCatalog : SignatureCatalogWellFormed active.signatures)
    (activeBinders : TypeParameterBindersWellFormed active)
    (instantiationValid :
      SourceSemantics.DataConstructorInstantiation.Admissible active
        (instantiation.applySubstitution later.inference.substitution))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext active)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base evidenceSource)
    (ownership : RequirementOwnership base evidenceSource)
    (activeSignaturesEq : active.signatures = base.signatures)
    (activeRequirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered evidenceSource active
      (.expression result.id)) :
    ExpressionTypingBase (resultState.toTypedSource roots) semanticSource active
      later.inference.substitution result := by
  have finish
      {argumentInitial argumentsState : Frontend.SourceInference.State}
      {inferredArguments : List InferredExpression}
      (argumentInitialReady : argumentInitial.InferenceReady)
      (payloadAtArgumentInitial : ∀ payload ∈ instantiation.payloadTypes,
        payload.VariablesBelow argumentInitial.inference.next)
      (resultAtArgumentInitial : instantiation.resultType.VariablesBelow
        argumentInitial.inference.next)
      (expectedAtArgumentInitial : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow argumentInitial.inference.next)
      (nodesAtArgumentInitial : argumentInitial.NodesBelowNextOccurrence)
      (argumentInitialInvariant : ActiveLocalContextInvariant argumentInitial
        later.inference.substitution active)
      (argumentInitialBindersBelow :
        argumentInitial.LocalBindersBelowNextLocal)
      (argumentsSuccess : Detail.inferConstructorArgumentsFuel fuel
        inferenceContext arguments instantiation.payloadTypes argumentInitial =
          .ok (inferredArguments, argumentsState))
      (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
        source id (argumentsState.resolve instantiation.resultType)
        (.constructor instantiation (inferredArguments.map (·.id))) []
        expected argumentsState none = .ok (result, resultState)) :
      ExpressionTypingBase (resultState.toTypedSource roots) semanticSource
        active later.inference.substitution result := by
    have argumentsProperties :=
      Detail.inferConstructorArgumentsFuel_inferenceProperties
        argumentInitialReady signatureFormation functionsCanonical
        payloadAtArgumentInitial argumentsSuccess
    have resultAtArguments : instantiation.resultType.VariablesBelow
        argumentsState.inference.next :=
      resultAtArgumentInitial.weaken argumentsProperties.1.next_le
    have resolvedResultBelow :
        (argumentsState.resolve instantiation.resultType).VariablesBelow
          argumentsState.inference.next :=
      argumentsProperties.2.1.solved.variablesBelow_apply resultAtArguments
    have expectedAtArguments : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow argumentsState.inference.next := by
      intro expectedType member
      exact (expectedAtArgumentInitial expectedType member).weaken
        argumentsProperties.1.next_le
    have recordProperties :=
      Detail.recordExpressionWithExpected_inferenceProperties
        argumentsProperties.2.1 resolvedResultBelow expectedAtArguments
        recordSuccess
    have outerArguments : later.inference.substitution.SemanticallyExtends
        argumentsState.inference.substitution :=
      TypeSystem.Substitution.SemanticallyExtends.trans substitutionExtends
        recordProperties.1.substitution_extends
    have argumentsIntegerLiteralsSubset :
        argumentsState.integerLiterals ⊆ evidenceState.integerLiterals := by
      intro origin member
      apply parentIntegerLiteralsSubset
      rw [Detail.recordExpressionWithExpected_integerLiterals_eq recordSuccess]
      exact member
    have argumentsRequirementsSubset :
        argumentsState.requirements ⊆ evidenceState.requirements :=
      List.Subset.trans
        (Detail.recordExpressionWithExpected_requirements_subset recordSuccess)
        parentRequirementsEvidenceSubset
    have evidence := argumentsEvidence argumentsSuccess recordSuccess
    have payloadAdmissible : ∀ payload ∈ instantiation.payloadTypes,
        TypeAdmissible active
          (later.inference.substitution.apply payload) := by
      intro payload member
      have appliedMember : later.inference.substitution.apply payload ∈
          (instantiation.applySubstitution
            later.inference.substitution).payloadTypes := by
        simpa [DataConstructorInstantiation.applySubstitution] using
          List.mem_map.mpr ⟨payload, member, rfl⟩
      exact
        SourceSemantics.DataConstructorInstantiation.Admissible.payload_type_admissible
          activeCatalog activeBinders instantiationValid appliedMember
    have argumentsType :=
      inferConstructorArgumentsFuel_success_expressionsHaveTypes_under_covered_retained_bounded
        fuel_lt argumentInitialReady signatureFormation functionsCanonical
        payloadAtArgumentInitial nodesAtArgumentInitial
        argumentInitialInvariant argumentInitialBindersBelow outerArguments
        argumentsIntegerLiteralsSubset argumentsRequirementsSubset
        evidence.retained evidence.childrenRetained evidence.covered
        evidence.preserved childSound payloadAdmissible argumentsSuccess
    exact
      recordExpressionWithExpected_success_constructor_expressionTypingBase_scoped_of_retained
        recordSuccess outerArguments argumentsType activeBinders
        instantiationValid substitutionExtends requirementsSubset retained
        traitSuccess profileSuccess catalog contextValid signaturesEq traitName
        solveSuccess solvedEq ledger ownership activeSignaturesEq
        activeRequirementsEq assumptionsMono covered
  unfold Detail.inferConstructorApplicationFuel at success
  by_cases arity : arguments.length = instantiation.payloadTypes.length
  · simp only [arity] at success
    cases expected with
    | none =>
        simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at success
        cases argumentsResult : Detail.inferConstructorArgumentsFuel fuel
            inferenceContext arguments instantiation.payloadTypes initial with
        | error error =>
            simp [argumentsResult] at success
        | ok argumentsPair =>
            rcases argumentsPair with ⟨inferredArguments, argumentsState⟩
            simp only [argumentsResult] at success
            exact finish ready payloadBelow resultBelow expectedBelow nodesBelow
              initialInvariant initialBindersBelow argumentsResult success
    | some expectedType =>
        cases unifyResult : Detail.unify initial instantiation.resultType
            expectedType with
        | error error =>
            simp [unifyResult, bind, Except.bind] at success
        | ok argumentInitial =>
            simp only [unifyResult, bind, Except.bind] at success
            have expectedTypeBelow : expectedType.VariablesBelow
                initial.inference.next :=
              expectedBelow expectedType (by simp)
            have unifyProgress := Detail.unify_inferenceProgress ready.solved
              resultBelow expectedTypeBelow unifyResult
            have argumentInitialReady :=
              Detail.unify_preserves_inferenceReady ready resultBelow
                expectedTypeBelow unifyResult
            have payloadAtArgumentInitial : ∀ payload ∈
                instantiation.payloadTypes,
                payload.VariablesBelow argumentInitial.inference.next := by
              intro payload member
              exact (payloadBelow payload member).weaken unifyProgress.next_le
            have resultAtArgumentInitial :
                instantiation.resultType.VariablesBelow
                  argumentInitial.inference.next :=
              resultBelow.weaken unifyProgress.next_le
            have expectedAtArgumentInitial : ∀ candidate ∈
                (some expectedType : Option TypeSystem.Ty),
                candidate.VariablesBelow argumentInitial.inference.next := by
              intro candidate member
              simp only [Option.mem_def] at member
              injection member with candidateEq
              subst candidate
              exact expectedTypeBelow.weaken unifyProgress.next_le
            have nodesAtArgumentInitial :
                argumentInitial.NodesBelowNextOccurrence :=
              (Detail.unify_occurrenceBoundExtends unifyResult
                ).nodesBelowNextOccurrence nodesBelow
            have argumentInitialInvariant : ActiveLocalContextInvariant
                argumentInitial later.inference.substitution active :=
              initialInvariant.unify unifyResult
            have argumentInitialBindersBelow :
                argumentInitial.LocalBindersBelowNextLocal :=
              Detail.unify_preserves_localBindersBelowNextLocal
                initialBindersBelow unifyResult
            cases argumentsResult : Detail.inferConstructorArgumentsFuel fuel
                inferenceContext arguments instantiation.payloadTypes
                argumentInitial with
            | error error =>
                simp [argumentsResult] at success
            | ok argumentsPair =>
                rcases argumentsPair with
                  ⟨inferredArguments, argumentsState⟩
                simp only [argumentsResult] at success
                exact finish argumentInitialReady payloadAtArgumentInitial
                  resultAtArgumentInitial expectedAtArgumentInitial
                  nodesAtArgumentInitial argumentInitialInvariant
                  argumentInitialBindersBelow argumentsResult success
  · simp [arity, bind, Except.bind] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
