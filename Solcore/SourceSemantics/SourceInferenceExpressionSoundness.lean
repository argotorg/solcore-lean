import Solcore.SourceSemantics.SourceInferenceSoundness
import Solcore.SourceSemantics.Dynamic.Control

/-!
The expression-level induction which closes source inference is deliberately
kept separate from the already large collection of shape lemmas.  This module
starts with the one shape which was not previously connected to
`ExpressionTypingBase`: lambdas.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference TypeSystem

private theorem functionParts?_success_eq
    {type parameter result : TypeSystem.Ty}
    (success : Detail.functionParts? type = some (parameter, result)) :
    type = .function parameter result := by
  cases type <;> simp_all [Detail.functionParts?]

/-- The compact lambda-prefix inversion exported by expression inference also
contains enough information to recover the usual progress/readiness facts.
Keeping this projection outside the recursive dispatcher avoids repeating the
four annotation/expectation cases in the eventual fuel induction. -/
theorem lambdaPrefixFacts_inferenceProperties
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState)
    (ready : parameterState.InferenceReady)
    (parameterTypeBelow :
      (TypeSystem.Ty.productMany parameterTypes).VariablesBelow
        parameterState.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow parameterState.inference.next) :
    parameterState.InferenceProgress resultState ∧
      resultState.InferenceReady ∧
      resultType.VariablesBelow resultState.inference.next := by
  have expectedPartsBelow {expectedParameter expectedResult : TypeSystem.Ty}
      (partsEq : expected.bind (fun type =>
        Detail.functionParts? (parameterState.resolve type)) =
          some (expectedParameter, expectedResult)) :
      expectedParameter.VariablesBelow parameterState.inference.next ∧
        expectedResult.VariablesBelow parameterState.inference.next := by
    simp only [Option.bind_eq_some_iff] at partsEq
    obtain ⟨expectedType, expectedEq, typePartsEq⟩ := partsEq
    have expectedAtParameter : expectedType.VariablesBelow
        parameterState.inference.next :=
      expectedBelow expectedType (by simp [expectedEq])
    have resolvedExpectedBelow :
        (parameterState.resolve expectedType).VariablesBelow
          parameterState.inference.next :=
      ready.solved.variablesBelow_apply expectedAtParameter
    exact Detail.functionParts?_success_variablesBelow resolvedExpectedBelow
      typePartsEq
  cases facts with
  | noExpectedPartsAnnotated _ _ resolution =>
      exact ⟨Frontend.SourceInference.State.InferenceProgress.refl
          ready.solved, ready,
        Detail.resolveSourceType_success_variablesBelow resolution _⟩
  | noExpectedPartsFresh _ _ freshEq =>
      have progress :=
        Frontend.SourceInference.State.InferenceProgress.fresh parameterState
          ready.solved
      have finalReady :=
        Frontend.SourceInference.State.InferenceReady.fresh ready
      have typeBelow : parameterState.fresh.1.VariablesBelow
          parameterState.fresh.2.inference.next := by
        change TypeSystem.Ty.VariablesBelow
          (parameterState.inference.next + 1)
          (.variable ⟨parameterState.inference.next⟩)
        exact (TypeSystem.Ty.variablesBelow_variable_iff _ _).2
          (Nat.lt_succ_self _)
      rw [freshEq] at progress finalReady typeBelow
      exact ⟨progress, finalReady, typeBelow⟩
  | expectedPartsAnnotated partsEq parameterUnify _ resolution =>
      have partsBelow := expectedPartsBelow partsEq
      have progress := Detail.unify_inferenceProgress ready.solved
        parameterTypeBelow partsBelow.1 parameterUnify
      have finalReady := Detail.unify_preserves_inferenceReady ready
        parameterTypeBelow partsBelow.1 parameterUnify
      have resultBelow : resultType.VariablesBelow
          parameterState.inference.next :=
        Detail.resolveSourceType_success_variablesBelow resolution _
      exact ⟨progress, finalReady, resultBelow.weaken progress.next_le⟩
  | expectedPartsInferred partsEq parameterUnify _ =>
      have partsBelow := expectedPartsBelow partsEq
      have progress := Detail.unify_inferenceProgress ready.solved
        parameterTypeBelow partsBelow.1 parameterUnify
      have finalReady := Detail.unify_preserves_inferenceReady ready
        parameterTypeBelow partsBelow.1 parameterUnify
      exact ⟨progress, finalReady, partsBelow.2.weaken progress.next_le⟩

/-- Lambda-prefix fitting changes inference information only; it leaves the
active executable binder stack, and hence its declarative alignment, intact. -/
theorem lambdaPrefixFacts_activeLocalContextInvariant
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState)
    (invariant : ActiveLocalContextInvariant parameterState substitution
      context) :
    ActiveLocalContextInvariant resultState substitution context := by
  cases facts with
  | noExpectedPartsAnnotated => exact invariant
  | noExpectedPartsFresh _ _ freshEq =>
      apply invariant.congr_localBinders
      have finalEq : parameterState.fresh.2 = resultState :=
        congrArg Prod.snd freshEq
      rw [← finalEq]
      rfl
  | expectedPartsAnnotated _ parameterUnify =>
      exact invariant.unify parameterUnify
  | expectedPartsInferred _ parameterUnify =>
      exact invariant.unify parameterUnify

/-- Lambda-prefix fitting never changes the stable-local allocator.  This is
the executable side-condition needed by a recursive statement proof for the
actual lambda body. -/
theorem lambdaPrefixFacts_localBindersBelowNextLocal
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState)
    (below : parameterState.LocalBindersBelowNextLocal) :
    resultState.LocalBindersBelowNextLocal := by
  cases facts with
  | noExpectedPartsAnnotated => exact below
  | noExpectedPartsFresh _ _ freshEq =>
      have preserved :=
        Frontend.SourceInference.State.fresh_preserves_localBindersBelowNextLocal
          parameterState below
      have finalEq : parameterState.fresh.2 = resultState :=
        congrArg Prod.snd freshEq
      rwa [finalEq] at preserved
  | expectedPartsAnnotated _ parameterUnify =>
      exact Detail.unify_preserves_localBindersBelowNextLocal below
        parameterUnify
  | expectedPartsInferred _ parameterUnify =>
      exact Detail.unify_preserves_localBindersBelowNextLocal below
        parameterUnify

/-- Lambda-prefix fitting allocates no source occurrence, so an occurrence
bound established after parameter binding is still available at the body
entry. -/
theorem lambdaPrefixFacts_nodesBelowNextOccurrence
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState)
    (below : parameterState.NodesBelowNextOccurrence) :
    resultState.NodesBelowNextOccurrence := by
  cases facts with
  | noExpectedPartsAnnotated => exact below
  | noExpectedPartsFresh _ _ freshEq =>
      have preserved :=
        Frontend.SourceInference.State.fresh_preserves_nodesBelowNextOccurrence
          parameterState below
      have finalEq : parameterState.fresh.2 = resultState :=
        congrArg Prod.snd freshEq
      rwa [finalEq] at preserved
  | expectedPartsAnnotated _ parameterUnify =>
      exact (Detail.unify_occurrenceBoundExtends parameterUnify
        ).nodesBelowNextOccurrence below
  | expectedPartsInferred _ parameterUnify =>
      exact (Detail.unify_occurrenceBoundExtends parameterUnify
        ).nodesBelowNextOccurrence below

/-- Lambda-prefix fitting preserves the declaration owner. -/
private theorem lambdaPrefixFacts_owner_eq
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState) :
    resultState.owner = parameterState.owner := by
  cases facts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ freshEq =>
      have finalEq : parameterState.fresh.2 = resultState :=
        congrArg Prod.snd freshEq
      rw [← finalEq]
      rfl
  | expectedPartsAnnotated _ parameterUnify =>
      exact congrArg (fun header : Frontend.SourceInference.State.Header =>
        header.owner) (Detail.unify_state_header parameterUnify)
  | expectedPartsInferred _ parameterUnify =>
      exact congrArg (fun header : Frontend.SourceInference.State.Header =>
        header.owner) (Detail.unify_state_header parameterUnify)

/-- Every result type selected by the executable lambda prefix is admissible
after final substitution.  An annotation is justified by source-type
formation, a fresh result by the residual-variable policy, and an inferred
result by projection from the admissible expected function type. -/
theorem lambdaPrefixFacts_resultTypeAdmissible_afterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {expected : Option TypeSystem.Ty}
    {returnAnnotation : Option Syntax.TypeExpr}
    {parameterTypes : List TypeSystem.Ty}
    {parameterState resultState : Frontend.SourceInference.State}
    {resultType : TypeSystem.Ty}
    {sourceContext active : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    {closedVariables : List TypeSystem.TypeVarId}
    (facts : Detail.LambdaPrefixFacts inferenceContext expected
      returnAnnotation parameterTypes parameterState resultType resultState)
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (binders : TypeParameterBindersWellFormed sourceContext)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid substitution
      closedVariables sourceContext active)
    (substitutionExtends : substitution.SemanticallyExtends
      parameterState.inference.substitution)
    (expectedAdmissible : ∀ expectedType ∈ expected,
      TypeAdmissible active (substitution.apply expectedType)) :
    TypeAdmissible active (substitution.apply resultType) := by
  cases facts with
  | noExpectedPartsAnnotated _ _ resolution =>
      apply FlexibleSubstitution.TypeAdmissible.applySubstitution
        contextValid.closes
      exact TypeAdmissible.ofWellFormed
        (resolveSourceType_success_typeWellFormed canonical signaturesEq
          parametersEq ownerEq resolution)
  | noExpectedPartsFresh _ _ freshEq =>
      have resultEq : parameterState.fresh.1 = resultType :=
        congrArg Prod.fst freshEq
      rw [← resultEq]
      change TypeAdmissible active
        (substitution.apply
          (.variable ⟨parameterState.inference.next⟩))
      apply FlexibleSubstitution.TypeAdmissible.applySubstitution
        contextValid.closes
      exact TypeAdmissible.variableOfResidual binders residual _
  | expectedPartsAnnotated _ _ _ resolution =>
      apply FlexibleSubstitution.TypeAdmissible.applySubstitution
        contextValid.closes
      exact TypeAdmissible.ofWellFormed
        (resolveSourceType_success_typeWellFormed canonical signaturesEq
          parametersEq ownerEq resolution)
  | @expectedPartsInferred expectedParameter _ _ partsEq _ _ =>
      simp only [Option.bind_eq_some_iff] at partsEq
      obtain ⟨expectedType, expectedEq, partsSuccess⟩ := partsEq
      have resolvedEq : parameterState.resolve expectedType =
          .function expectedParameter resultType :=
        functionParts?_success_eq partsSuccess
      have endpointEq : substitution.apply
          (parameterState.resolve expectedType) =
          substitution.apply expectedType := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            substitutionExtends expectedType
      have functionAdmissible : TypeAdmissible active
          (.function (substitution.apply expectedParameter)
            (substitution.apply resultType)) := by
        rw [← FlexibleSubstitution.apply_function, ← resolvedEq,
          endpointEq]
        exact expectedAdmissible expectedType (by simp [expectedEq])
      exact functionAdmissible.function_result

/-- Close the ordinary-recording tail of a lambda once parameter binding and
the recursively inferred body have been reconstructed declaratively.

`lambdaState` is the state after body-result unification and lexical-scope
restoration.  The progress premise is precisely what identifies its resolved
parameter and result annotations with the types seen by the enclosing final
substitution. -/
theorem
    recordExpressionWithExpected_success_lambda_expressionTypingBase_scoped_of_retained
    {inferenceContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {id : ExpressionId}
    {parameters : List TypedBinder} {parameterTypes : List TypeSystem.Ty}
    {resultType : TypeSystem.Ty} {body : List StatementId}
    {expected : Option TypeSystem.Ty}
    {lambdaState later : Frontend.SourceInference.State}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active lambdaContext bodyFinal :
      SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    {bodyFacts : BodyFacts}
    (recordSuccess : Detail.recordExpressionWithExpected inferenceContext
      expression id
      (.function
        (lambdaState.resolve (TypeSystem.Ty.productMany parameterTypes))
        (lambdaState.resolve resultType))
      (.lambda parameters (lambdaState.resolve resultType) body)
      [] expected lambdaState = .ok result)
    (lambdaProgress : lambdaState.InferenceProgress later)
    (namesUnique : (parameters.map (fun binder => binder.name)).Nodup)
    (parametersExtend : MonoBindersExtend semanticSource.owner active
      (parameters.map
        (TypedBinder.applySubstitution later.inference.substitution))
      (parameterTypes.map later.inference.substitution.apply) lambdaContext)
    (bodyType : StatementsHaveType semanticSource {
        returnType := later.inference.substitution.apply resultType
        loopDepth := 0
      } lambdaContext body bodyFinal bodyFacts)
    (bodyCompletes : BodyCompletes
      (later.inference.substitution.apply resultType) bodyFacts)
    (activeBinders : TypeParameterBindersWellFormed active)
    (resultAdmissible : TypeAdmissible active
      (later.inference.substitution.apply resultType))
    (substitutionExtends : later.inference.substitution.SemanticallyExtends
      result.2.inference.substitution)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
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
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots) semanticSource active
      later.inference.substitution result.1 := by
  have parameterResolved :
      later.inference.substitution.apply
          (lambdaState.resolve (TypeSystem.Ty.productMany parameterTypes)) =
        TypeSystem.Ty.productMany
          (parameterTypes.map later.inference.substitution.apply) := by
    calc
      later.inference.substitution.apply
          (lambdaState.resolve (TypeSystem.Ty.productMany parameterTypes)) =
          later.inference.substitution.apply
            (TypeSystem.Ty.productMany parameterTypes) := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            lambdaProgress.substitution_extends
              (TypeSystem.Ty.productMany parameterTypes)
      _ = TypeSystem.Ty.productMany
          (parameterTypes.map later.inference.substitution.apply) := by
        exact FlexibleSubstitution.apply_productMany _ _
  have resultResolved :
      later.inference.substitution.apply (lambdaState.resolve resultType) =
        later.inference.substitution.apply resultType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        lambdaProgress.substitution_extends resultType
  have formType : ExpressionFormHasRawType semanticSource active
      ((ExpressionForm.lambda parameters (lambdaState.resolve resultType)
        body).applySubstitution later.inference.substitution)
      (later.inference.substitution.apply
        (.function
          (lambdaState.resolve (TypeSystem.Ty.productMany parameterTypes))
          (lambdaState.resolve resultType)))
      (.ordinary []) := by
    rw [show later.inference.substitution.apply
          (.function
            (lambdaState.resolve (TypeSystem.Ty.productMany parameterTypes))
            (lambdaState.resolve resultType)) =
        .function
          (TypeSystem.Ty.productMany
            (parameterTypes.map later.inference.substitution.apply))
          (later.inference.substitution.apply resultType) by
      simp only [FlexibleSubstitution.apply_function, parameterResolved,
        resultResolved]]
    simpa [ExpressionForm.applySubstitution, resultResolved] using
      (ExpressionFormHasRawType.lambda
        (source := semanticSource)
        (by simpa [List.map_map, Function.comp_def,
          TypedBinder.applySubstitution] using namesUnique)
        parametersExtend bodyType bodyCompletes)
  have rawAdmissible : TypeAdmissible active
      (later.inference.substitution.apply
        (.function
          (lambdaState.resolve (TypeSystem.Ty.productMany parameterTypes))
          (lambdaState.resolve resultType))) := by
    rw [show later.inference.substitution.apply
          (.function
            (lambdaState.resolve (TypeSystem.Ty.productMany parameterTypes))
            (lambdaState.resolve resultType)) =
        .function
          (TypeSystem.Ty.productMany
            (parameterTypes.map later.inference.substitution.apply))
          (later.inference.substitution.apply resultType) by
      simp only [FlexibleSubstitution.apply_function, parameterResolved,
        resultResolved]]
    exact TypeAdmissible.function
      (parametersExtend.product_type_admissible activeBinders)
      resultAdmissible
  exact
    recordExpressionWithExpected_success_ordinaryExpressionTypingBase_scoped_of_retained
      recordSuccess substitutionExtends requirementsSubset retained formType
      rawAdmissible traitSuccess profileSuccess catalog contextValid
      signaturesEq traitName solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered

/-- Parameter binding changes the lexical and inference portions of a state,
but never its declaration header.  The frontend keeps this fact private to
its large mutual preservation proof; the lambda bridge only needs the owner
projection, so it is reproved locally from the executable traversal. -/
private theorem bindLambdaParameters_owner_eq
    {inferenceContext : Frontend.SourceInference.Context}
    {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String}
    {state : Frontend.SourceInference.State}
    {result : List TypedBinder × List TypeSystem.Ty ×
      Frontend.SourceInference.State}
    (success : Detail.bindLambdaParameters inferenceContext parameters index
      seen state = .ok result) :
    result.2.2.owner = state.owner := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [Detail.bindLambdaParameters] at success
      injection success with resultEq
      subst result
      rfl
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [Detail.bindLambdaParameters, parameterValue, bind,
            Except.bind] at success
      | inferred name =>
          simp only [Detail.bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all
          all_goals
            subst result
            subst_vars
            have tailOwner := induction _ _ _ (by assumption)
            exact tailOwner.trans (by
              simp_all [Frontend.SourceInference.State.fresh,
                Frontend.SourceInference.State.allocateBinder])
      | typed marker name sourceType =>
          simp only [Detail.bindLambdaParameters, parameterValue] at success
          cases typeResult : Detail.resolveSourceType inferenceContext
              sourceType with
          | error error =>
              simp [typeResult, bind, Except.bind] at success
          | ok type =>
              simp only [typeResult, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all
              all_goals
                subst result
                subst_vars
                have tailOwner := induction _ _ _ (by assumption)
                exact tailOwner.trans (by
                  simp_all [Frontend.SourceInference.State.allocateBinder])

/-- The final expected-type fit preserves the complete input node prefix and
then appends the lambda node. -/
private theorem recordExpressionWithExpected_success_nodesPrefix
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {type : TypeSystem.Ty} {form : ExpressionForm}
    {requirements : List RequirementId}
    {expected : Option TypeSystem.Ty}
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

private theorem addRequirementsWithIds_integerPatterns_eq
    (state : Frontend.SourceInference.State)
    (predicates : List ProgramPredicate) :
    (state.addRequirementsWithIds predicates).2.integerPatterns =
      state.integerPatterns := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate predicates induction =>
      simp only [Frontend.SourceInference.State.addRequirementsWithIds]
      exact (induction (state.addRequirementWithId predicate).2).trans rfl

private theorem commitCoercionPlan_integerPatterns_eq
    (state : Frontend.SourceInference.State)
    (plan : List Detail.PlannedCoercionStep) :
    (Detail.commitCoercionPlan state plan).2.integerPatterns =
      state.integerPatterns := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [Detail.commitCoercionPlan]
      exact (induction
        ((state.addRequirementWithId step.predicate).2
          |>.addRequirementsWithIds step.methodPredicates).2).trans
        ((addRequirementsWithIds_integerPatterns_eq
          (state.addRequirementWithId step.predicate).2
          step.methodPredicates).trans rfl)

/-- Expected-type fitting and recording do not change numeric-pattern
origins.  This local public-facing projection mirrors the corresponding
frontend preservation fact, which is intentionally private there. -/
theorem recordExpressionWithExpected_integerPatterns_eq
    {inferenceContext : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {type : TypeSystem.Ty} {form : ExpressionForm}
    {requirements : List RequirementId}
    {expected : Option TypeSystem.Ty}
    {initial : Frontend.SourceInference.State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.recordExpressionWithExpected inferenceContext source id
      type form requirements expected initial localSchemeInstantiationStart =
        .ok result) :
    result.2.integerPatterns = initial.integerPatterns := by
  unfold Detail.recordExpressionWithExpected at success
  cases fittedResult : Detail.withExpected inferenceContext initial { id, type }
      expected with
  | error error =>
      simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind] at success
      change Except.ok (Detail.recordExpression source fitted.expression form
        (requirements ++ Detail.coercionRequirements fitted.coercions)
        fitted.coercions fitted.state localSchemeInstantiationStart) =
          Except.ok result at success
      injection success with resultEq
      subst result
      change fitted.state.integerPatterns = initial.integerPatterns
      unfold Detail.withExpected at fittedResult
      cases expected with
      | none =>
          injection fittedResult with fittedEq
          subst fitted
          rfl
      | some expectedType =>
          cases unification : initial.inference.unify type expectedType with
          | ok inference =>
              simp only [unification] at fittedResult
              injection fittedResult with fittedEq
              subst fitted
              rfl
          | error unificationError =>
              cases unificationError with
              | occursCheck metavariable failedType =>
                  simp [unification] at fittedResult
              | exhausted =>
                  simp [unification] at fittedResult
              | mismatch left right =>
                  simp only [unification] at fittedResult
                  cases planResult : Detail.coercionPlan? inferenceContext
                      initial (initial.resolve type)
                      (initial.resolve expectedType) with
                  | error error =>
                      simp [planResult, bind, Except.bind] at fittedResult
                  | ok plan? =>
                      cases plan? with
                      | none =>
                          simp [planResult, bind, Except.bind] at fittedResult
                      | some plan =>
                          simp only [planResult, bind, Except.bind] at fittedResult
                          change Except.ok _ = Except.ok fitted at fittedResult
                          injection fittedResult with fittedEq
                          subst fitted
                          exact commitCoercionPlan_integerPatterns_eq
                            initial plan

/-- The successful lambda branch of `inferExprFuel`, connected to the
declarative lambda rule.

The recursive statement premise is restricted to the actual body trace at
the exact predecessor fuel.  The bridge supplies that trace's readiness,
allocator bounds, local invariant, source extension, whole-result ledgers,
and per-root scope coverage.  The final result admissibility supplied by
whole-body finalization also closes the expected-function prefix; annotations
and fresh results are handled directly by
`lambdaPrefixFacts_resultTypeAdmissible_afterSubstitution`. -/
theorem inferExprFuel_success_lambda_expressionTypingBase_scoped_of_retained
    {fuel : Nat}
    {inferenceContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {keyword : Syntax.SourceSpan}
    {sourceParameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {returnAnnotation : Option Syntax.TypeExpr} {body : Syntax.Block}
    {expected : Option TypeSystem.Ty}
    {initial allocated later evidenceState : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    {roots : List NodeId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base active : SourceSemantics.Context}
    {semanticSource evidenceSource : TypedSource}
    {closedVariables : List TypeSystem.TypeVarId}
    (expressionEq : expression.value =
      .lambda keyword sourceParameters returnAnnotation body)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) inferenceContext expression
      expected initial = .ok result)
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow initial.inference.next)
    (initialNodesBelow : initial.NodesBelowNextOccurrence)
    (resultProgress : result.2.InferenceProgress later)
    (allocatedInvariant : ActiveLocalContextInvariant allocated
      later.inference.substitution active)
    (allocatedBelow : allocated.LocalBindersBelowNextLocal)
    (sourceOwner : semanticSource.owner = allocated.owner)
    (resultSourceExtension : TypingSourceExtends
      ((result.2.toTypedSource roots).applySubstitution
        later.inference.substitution) semanticSource)
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (sourceBinders : TypeParameterBindersWellFormed sourceContext)
    (activeBinders : TypeParameterBindersWellFormed active)
    (parametersEq : sourceContext.typeParameters =
      inferenceContext.typeParameters)
    (ownerEq : sourceContext.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (residual : sourceContext.residualTypeVariables = true)
    (finalResultAdmissible : TypeAdmissible active
      (later.inference.substitution.apply result.1.type))
    (bodySound :
      ∀ {resultType : TypeSystem.Ty}
        {childInitial : Frontend.SourceInference.State}
        {childResult : Detail.BlockResult}
        {childContext : SourceSemantics.Context},
        childInitial.InferenceReady →
          resultType.VariablesBelow childInitial.inference.next →
          childInitial.NodesBelowNextOccurrence →
          childInitial.LocalBindersBelowNextLocal →
          ActiveLocalContextInvariant childInitial
            later.inference.substitution childContext →
          Detail.inferStatementsFuel fuel
              { inferenceContext with loopDepth := 0 }
              body.value resultType childInitial = .ok childResult →
          later.inference.substitution.SemanticallyExtends
            childResult.state.inference.substitution →
          TypingSourceExtends
            ((childResult.state.toTypedSource roots).applySubstitution
              later.inference.substitution) semanticSource →
          childResult.state.integerPatterns ⊆
            evidenceState.integerPatterns →
          childResult.state.integerLiterals ⊆
            evidenceState.integerLiterals →
          childResult.state.requirements ⊆ evidenceState.requirements →
          (∀ statement ∈ childResult.statements,
            TemplateScopeCovered evidenceSource childContext
              (.statement statement)) →
          ∃ finalContext bodyFacts,
            ActiveLocalContextInvariant childResult.state
                later.inference.substitution finalContext ∧
              StatementsHaveType semanticSource {
                returnType := later.inference.substitution.apply resultType
                loopDepth := 0
              } childContext childResult.statements finalContext bodyFacts ∧
              BlockResultMatchesFactsAfterSubstitution
                later.inference.substitution childResult bodyFacts)
    (integerPatternsToEvidence :
      result.2.integerPatterns ⊆ evidenceState.integerPatterns)
    (integerLiteralsToEvidence :
      result.2.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsToEvidence :
      result.2.requirements ⊆ evidenceState.requirements)
    (directChildrenRetained : ∀ {child : NodeId},
      DirectChild (result.2.toTypedSource roots)
          (.expression result.1.id) child →
        DirectChild evidenceSource (.expression result.1.id) child)
    (evidenceClosed : OccurrenceGraphClosed evidenceSource)
    (requirementsSubset : result.2.requirements ⊆ later.requirements)
    (retained : ExpressionRequirementsRetainedAt
      (result.2.toTypedSource roots) evidenceSource result.1.id)
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
      (.expression result.1.id)) :
    ExpressionTypingBase (result.2.toTypedSource roots) semanticSource active
      later.inference.substitution result.1 := by
  obtain ⟨boundParameters, parameterTypes, parameterState, resultType,
      resultState, bodyResult, unifiedState, restoredState, parametersSuccess,
      prefixFacts, bodySuccess, unifySuccess, restoredEq, recordSuccess⟩ :=
    Detail.inferExprFuel_success_lambda_facts expressionEq allocationEq success
  have allocationProgress : initial.InferenceProgress allocated := by
    have progress :=
      Frontend.SourceInference.State.InferenceProgress.allocateExpressionId
        initial ready.solved
    rw [allocationEq] at progress
    exact progress
  have allocatedReady : allocated.InferenceReady := by
    have nextReady :=
      Frontend.SourceInference.State.InferenceReady.allocateExpressionId ready
    rw [allocationEq] at nextReady
    exact nextReady
  have parameterProperties :=
    Detail.bindLambdaParameters_inferenceProperties allocatedReady
      parametersSuccess
  have parameterTypeBelow :
      (TypeSystem.Ty.productMany parameterTypes).VariablesBelow
        parameterState.inference.next :=
    TypeSystem.Ty.variablesBelow_productMany parameterProperties.2.2
  have expectedAtParameter : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow parameterState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (allocationProgress.trans parameterProperties.1).next_le
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts
    parameterProperties.2.1 parameterTypeBelow expectedAtParameter
  have lambdaSignatureFormation : ProgramSignatureFormationValidated
      ({ inferenceContext with loopDepth := 0 } :
        Frontend.SourceInference.Context).signatures := by
    simpa using signatureFormation
  have lambdaFunctionsCanonical : ∀ signature ∈
      ({ inferenceContext with loopDepth := 0 } :
        Frontend.SourceInference.Context).signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes) := by
    simpa using functionsCanonical
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with loopDepth := 0 })
    prefixProperties.2.1 lambdaSignatureFormation lambdaFunctionsCanonical
      prefixProperties.2.2 bodySuccess
  have resultAtBody : resultType.VariablesBelow
      bodyResult.state.inference.next :=
    prefixProperties.2.2.weaken bodyProperties.1.next_le
  have unifiedProgress := Detail.unify_inferenceProgress
    bodyProperties.2.1.solved bodyProperties.2.2 resultAtBody unifySuccess
  have unifiedReady := Detail.unify_preserves_inferenceReady
    bodyProperties.2.1 bodyProperties.2.2 resultAtBody unifySuccess
  have restoreStep : unifiedState.InferenceProgress restoredState := by
    rw [restoredEq]
    exact Frontend.SourceInference.State.InferenceProgress.restoreLexicalScope
      unifiedState allocated.lexicalScope unifiedReady.solved
  have throughUnified : allocated.InferenceProgress unifiedState :=
    parameterProperties.1.trans
      (prefixProperties.1.trans
        (bodyProperties.1.trans unifiedProgress))
  have restoredProperties : allocated.InferenceProgress restoredState ∧
      restoredState.InferenceReady := by
    rw [restoredEq]
    exact Frontend.SourceInference.State.restoreLexicalScope_inferenceProperties
      allocatedReady throughUnified
  have parameterToRestored :
      parameterState.InferenceProgress restoredState :=
    prefixProperties.1.trans
      (bodyProperties.1.trans (unifiedProgress.trans restoreStep))
  have resultToRestored : resultState.InferenceProgress restoredState :=
    bodyProperties.1.trans (unifiedProgress.trans restoreStep)
  have resolvedParameterBelow :
      (restoredState.resolve
        (TypeSystem.Ty.productMany parameterTypes)).VariablesBelow
          restoredState.inference.next :=
    parameterToRestored.resolve_variablesBelow parameterTypeBelow
  have resolvedResultBelow :
      (restoredState.resolve resultType).VariablesBelow
        restoredState.inference.next :=
    resultToRestored.resolve_variablesBelow prefixProperties.2.2
  have functionBelow :
      (TypeSystem.Ty.function
        (restoredState.resolve (TypeSystem.Ty.productMany parameterTypes))
        (restoredState.resolve resultType)).VariablesBelow
          restoredState.inference.next :=
    (TypeSystem.Ty.variablesBelow_function_iff _ _ _).2
      ⟨resolvedParameterBelow, resolvedResultBelow⟩
  have expectedAtRestored : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow restoredState.inference.next := by
    intro expectedType member
    exact (expectedBelow expectedType member).weaken
      (allocationProgress.trans restoredProperties.1).next_le
  have recordProperties :=
    Detail.recordExpressionWithExpected_inferenceProperties
      restoredProperties.2 functionBelow expectedAtRestored recordSuccess
  have restoredProgress : restoredState.InferenceProgress later :=
    recordProperties.1.trans resultProgress
  have parameterProgress : parameterState.InferenceProgress later :=
    parameterToRestored.trans restoredProgress
  have parameterTypesAdmissible :=
    bindLambdaParameters_success_typesAdmissible_afterSubstitution
      parametersSuccess canonical sourceBinders signaturesEq parametersEq
      ownerEq residual contextValid
  obtain ⟨lambdaContext, namesUnique, _, parametersExtend,
      parameterInvariant, parameterBindersBelow⟩ :=
    bindLambdaParameters_success_monoBindersExtend_afterSubstitution
      parametersSuccess allocatedInvariant allocatedBelow
      parameterTypesAdmissible
  have parametersExtendSource : MonoBindersExtend semanticSource.owner active
      (boundParameters.map
        (TypedBinder.applySubstitution later.inference.substitution))
      (parameterTypes.map later.inference.substitution.apply)
      lambdaContext := by
    simpa only [sourceOwner] using parametersExtend
  have resultInvariant : ActiveLocalContextInvariant resultState
      later.inference.substitution lambdaContext :=
    lambdaPrefixFacts_activeLocalContextInvariant prefixFacts
      parameterInvariant
  have allocatedNodesBelow : allocated.NodesBelowNextOccurrence := by
    have preserved :=
      Frontend.SourceInference.State.allocateExpressionId_preserves_nodesBelowNextOccurrence
        initial initialNodesBelow
    have finalEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rwa [finalEq] at preserved
  have parameterNodesBelow : parameterState.NodesBelowNextOccurrence :=
    (Detail.bindLambdaParameters_occurrenceBoundExtends parametersSuccess
      ).nodesBelowNextOccurrence allocatedNodesBelow
  have resultNodesBelow : resultState.NodesBelowNextOccurrence :=
    lambdaPrefixFacts_nodesBelowNextOccurrence prefixFacts parameterNodesBelow
  have resultBindersBelow : resultState.LocalBindersBelowNextLocal :=
    lambdaPrefixFacts_localBindersBelowNextLocal prefixFacts
      parameterBindersBelow
  have allocatedOwner : allocated.owner = initial.owner := by
    have finalEq : initial.allocateExpressionId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← finalEq]
    rfl
  have parameterOwner : parameterState.owner = allocated.owner :=
    bindLambdaParameters_owner_eq parametersSuccess
  have prefixOwner : resultState.owner = parameterState.owner :=
    lambdaPrefixFacts_owner_eq prefixFacts
  have bodyOwner : bodyResult.state.owner = resultState.owner :=
    Detail.inferStatementsFuel_preserves_owner bodySuccess
  have bodyToResultRaw : TypingSourceExtends
      (bodyResult.state.toTypedSource roots)
      (result.2.toTypedSource roots) := by
    constructor
    · exact (Detail.inferExprFuel_preserves_owner success).trans
        (allocatedOwner.symm.trans
          (parameterOwner.symm.trans
            (prefixOwner.symm.trans bodyOwner.symm)))
    · have nodesPrefix :=
        recordExpressionWithExpected_success_nodesPrefix recordSuccess
      have unifyNodes := (Detail.unify_occurrenceState_eq unifySuccess).1
      rw [restoredEq,
        Frontend.SourceInference.State.restoreLexicalScope_nodes,
        unifyNodes] at nodesPrefix
      exact nodesPrefix
  have bodySourceExtension : TypingSourceExtends
      ((bodyResult.state.toTypedSource roots).applySubstitution
        later.inference.substitution) semanticSource :=
    (bodyToResultRaw.applySubstitution later.inference.substitution).trans
      resultSourceExtension
  have laterExtendsUnified : later.inference.substitution.SemanticallyExtends
      unifiedState.inference.substitution := by
    have extendsRestored := restoredProgress.substitution_extends
    rw [restoredEq] at extendsRestored
    exact extendsRestored
  have laterExtendsBody : later.inference.substitution.SemanticallyExtends
      bodyResult.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans laterExtendsUnified
      unifiedProgress.substitution_extends
  have bodyIntegerPatternsToResult :
      bodyResult.state.integerPatterns ⊆ result.2.integerPatterns := by
    intro origin member
    rw [recordExpressionWithExpected_integerPatterns_eq recordSuccess,
      restoredEq]
    change origin ∈ unifiedState.integerPatterns
    rw [Detail.unify_integerPatterns unifySuccess]
    exact member
  have bodyIntegerLiteralsToResult :
      bodyResult.state.integerLiterals ⊆ result.2.integerLiterals := by
    intro origin member
    rw [Detail.recordExpressionWithExpected_integerLiterals_eq recordSuccess,
      restoredEq]
    change origin ∈ unifiedState.integerLiterals
    rw [Detail.unify_integerLiterals unifySuccess]
    exact member
  have bodyRequirementsToResult :
      bodyResult.state.requirements ⊆ result.2.requirements := by
    apply List.Subset.trans ?_
      (Detail.recordExpressionWithExpected_requirements_subset recordSuccess)
    rw [restoredEq]
    change bodyResult.state.requirements ⊆ unifiedState.requirements
    rw [Detail.unify_requirements_eq unifySuccess]
    exact fun _ member => member
  have bodyIntegerPatternsToEvidence :
      bodyResult.state.integerPatterns ⊆ evidenceState.integerPatterns :=
    List.Subset.trans bodyIntegerPatternsToResult integerPatternsToEvidence
  have bodyIntegerLiteralsToEvidence :
      bodyResult.state.integerLiterals ⊆ evidenceState.integerLiterals :=
    List.Subset.trans bodyIntegerLiteralsToResult integerLiteralsToEvidence
  have bodyRequirementsToEvidence :
      bodyResult.state.requirements ⊆ evidenceState.requirements :=
    List.Subset.trans bodyRequirementsToResult requirementsToEvidence
  obtain ⟨coercions, recordedContains⟩ :=
    recordExpressionWithExpected_success_containsExpression recordSuccess roots
  let lambdaNode : ExpressionNode := {
    id := result.1.id
    span := expression.span
    type := result.1.type
    form := .lambda boundParameters (restoredState.resolve resultType)
      bodyResult.statements
    requirements := [] ++ Detail.coercionRequirements coercions
    coercions
  }
  have containsLambda : ContainsExpression (result.2.toTypedSource roots)
      result.1.id lambdaNode := by
    simpa only [lambdaNode] using recordedContains
  have bodyCovered : ∀ statement ∈ bodyResult.statements,
      TemplateScopeCovered evidenceSource lambdaContext
        (.statement statement) := by
    intro statement member
    have rawEdge : DirectChild (result.2.toTypedSource roots)
        (.expression result.1.id) (.statement statement) := by
      refine ⟨.expression lambdaNode, ?_, ?_⟩
      · exact ⟨containsLambda.1,
          congrArg NodeId.expression containsLambda.2⟩
      · simpa [lambdaNode, nodeChildIds, Node.references,
          ExpressionForm.references] using
          (List.mem_map.mpr ⟨statement, member, rfl⟩ :
            (.statement statement : NodeId) ∈
              bodyResult.statements.map NodeId.statement)
    apply TemplateScopeCovered.expressionStatementChild covered
      evidenceClosed (directChildrenRetained rawEdge)
    intro predicate predicateMember
    rw [MonoBindersExtend.assumptions_eq parametersExtendSource]
    exact predicateMember
  obtain ⟨bodyFinal, bodyFacts, _, bodyType, bodyAgreement⟩ :=
    bodySound prefixProperties.2.1 prefixProperties.2.2 resultNodesBelow
      resultBindersBelow resultInvariant bodySuccess laterExtendsBody
      bodySourceExtension bodyIntegerPatternsToEvidence
      bodyIntegerLiteralsToEvidence bodyRequirementsToEvidence bodyCovered
  have unifiedTypesEq : later.inference.substitution.apply bodyResult.type =
      later.inference.substitution.apply resultType := by
    calc
      later.inference.substitution.apply bodyResult.type =
          later.inference.substitution.apply
            (unifiedState.resolve bodyResult.type) := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            (laterExtendsUnified bodyResult.type).symm
      _ = later.inference.substitution.apply
          (unifiedState.resolve resultType) :=
        congrArg later.inference.substitution.apply
          (Detail.unify_resolve_eq unifySuccess)
      _ = later.inference.substitution.apply resultType := by
        simpa [Frontend.SourceInference.State.resolve,
          TypeSystem.InferState.resolve] using
            laterExtendsUnified resultType
  have bodyFactsType : bodyFacts.type =
      later.inference.substitution.apply resultType :=
    bodyAgreement.type_eq.trans unifiedTypesEq
  have bodyCompletes : BodyCompletes
      (later.inference.substitution.apply resultType) bodyFacts :=
    bodyType.bodyCompletes_of_closed rfl bodyFactsType
  have expectedAdmissible : ∀ expectedType ∈ expected,
      TypeAdmissible active
        (later.inference.substitution.apply expectedType) := by
    intro expectedType member
    simp only [Option.mem_def] at member
    subst expected
    have resultExpectedEq :
        later.inference.substitution.apply result.1.type =
          later.inference.substitution.apply expectedType :=
      Detail.inferExprFuel_expected_type_apply_eq success
        resultProgress.substitution_extends
    rw [← resultExpectedEq]
    exact finalResultAdmissible
  have resultAdmissible : TypeAdmissible active
      (later.inference.substitution.apply resultType) :=
    lambdaPrefixFacts_resultTypeAdmissible_afterSubstitution prefixFacts
      canonical sourceBinders signaturesEq parametersEq ownerEq residual
      contextValid parameterProgress.substitution_extends expectedAdmissible
  exact
    recordExpressionWithExpected_success_lambda_expressionTypingBase_scoped_of_retained
      recordSuccess restoredProgress namesUnique parametersExtendSource
      bodyType bodyCompletes activeBinders
      resultAdmissible resultProgress.substitution_extends
      requirementsSubset retained traitSuccess profileSuccess catalog
      contextValid signaturesEq traitName solveSuccess solvedEq ledger
      ownership activeSignaturesEq activeRequirementsEq assumptionsMono covered

end Solcore.SourceSemantics.SourceInferenceSoundness
