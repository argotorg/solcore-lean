import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimes
import Solcore.SourceSemantics.SourceInferenceLambdaOperationalPrefix

/-! A lambda continuation transports any actual inner generalization, including
header declarations, through its real return unification and scope restore. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

private theorem parameter_binders_subset
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State}
    {result : List TypedBinder × List Ty × State}
    (accepted : bindLambdaParameters context parameters index seen initial = .ok result) :
    initial.localBinders ⊆ result.2.2.localBinders := by
  induction parameters generalizing index seen initial result with
  | nil =>
    simp only [bindLambdaParameters, Except.ok.injEq] at accepted
    cases accepted
    exact List.Subset.refl _
  | cons parameter rest ih =>
    cases form : parameter.value with
    | error => simp [bindLambdaParameters, form, bind, Except.bind] at accepted
    | inferred name =>
      simp only [bindLambdaParameters, form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals try simp_all
      all_goals
        subst result
        subst_vars
        exact (List.subset_cons_self _ _).trans (ih _ _ _ (by assumption))
    | typed marker name sourceType =>
      simp only [bindLambdaParameters, form] at accepted
      cases resolved : resolveSourceType context sourceType with
      | error error => simp [resolved, bind, Except.bind] at accepted
      | ok type =>
        simp only [resolved, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals try simp_all
        all_goals
          subst result
          subst_vars
          exact (List.subset_cons_self _ _).trans (ih _ _ _ (by assumption))

private theorem prefix_binders
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty}
    (facts : LambdaPrefixFacts context expected annotation types initial resultType final) :
    final.localBinders = initial.localBinders := by
  cases facts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ fresh =>
    rw [← show initial.fresh.2 = final from congrArg Prod.snd fresh]
    rfl
  | expectedPartsAnnotated _ unified | expectedPartsInferred _ unified =>
    exact congrArg LexicalScope.binders (unify_preserves_lexicalScope unified)

theorem GeneralizationLifetime.finishLambda
    {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {childFuel : Nat}
    {context : SourceInference.Context} {expression : Syntax.Expr}
    {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {annotation : Option Syntax.TypeExpr}
    {body : Syntax.Block} {expected : Option Ty} {initial : State}
    {boundParameters : List TypedBinder} {parameterTypes : List Ty} {parameterState : State}
    {resultType : Ty} {prefixState : State} {bodyResult : BlockResult}
    {unifiedState restoredState : State} {final : InferredExpression × State}
    (lifetime : GeneralizationLifetime event prefixState.inference.next bodyResult.state [bodyResult.type])
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (parametersRun : bindLambdaParameters context parameters.elements 0 []
      initial.allocateExpressionId.2 = .ok (boundParameters, parameterTypes, parameterState))
    (prefixFacts : LambdaPrefixFacts context expected annotation parameterTypes parameterState resultType prefixState)
    (bodyRun : inferStatementsFuel childFuel {context with loopDepth := 0}
      body.value resultType prefixState = .ok bodyResult)
    (unified : Detail.unify bodyResult.state bodyResult.type resultType = .ok unifiedState)
    (restoredEq : restoredState = unifiedState.restoreLexicalScope initial.allocateExpressionId.2.lexicalScope)
    (recorded : recordExpressionWithExpected context expression initial.allocateExpressionId.1
      (.function (restoredState.resolve (Ty.productMany parameterTypes)) (restoredState.resolve resultType))
      (.lambda boundParameters (restoredState.resolve resultType) bodyResult.statements)
      [] expected restoredState = .ok final) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  let protectedVars := binder.scheme.quantified
  let allocated := initial.allocateExpressionId.2
  have allocation : initial.InferenceProgress allocated := .allocateExpressionId _ ready.solved
  have parametersProperties := bindLambdaParameters_inferenceProperties ready.allocateExpressionId parametersRun
  have parameterBelow := Ty.variablesBelow_productMany parametersProperties.2.2
  have initialToParameter := allocation.trans parametersProperties.1
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts parametersProperties.2.1
    parameterBelow (fun type member => (expectedBelow type member).weaken initialToParameter.next_le)
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) prefixProperties.2.1 formation canonical
    prefixProperties.2.2 bodyRun
  have unifiedProgress := unify_inferenceProgress bodyProperties.2.1.solved bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady bodyProperties.2.1 bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedPrivacy : SafeTransport protectedVars bodyResult.state unifiedState :=
    ProtectedVariables.unify (lifetime.values _ (List.mem_singleton_self _)) (lifetime.older resultType prefixProperties.2.2) unified
  have parametersToUnified := prefixProperties.1.trans (bodyProperties.1.trans unifiedProgress)
  have allocatedToUnified := parametersProperties.1.trans parametersToUnified
  have restoredProperties := State.restoreLexicalScope_inferenceProperties ready.allocateExpressionId allocatedToUnified
  subst restoredState
  let restored := unifiedState.restoreLexicalScope allocated.lexicalScope
  have restoredReady : restored.InferenceReady := restoredProperties.2
  have restorePrivacy : SafeTransport protectedVars unifiedState restored := .of_substitution_eq rfl
  have restoreProgress : unifiedState.InferenceProgress restored := .restoreLexicalScope _ _ unifiedReady.solved
  have bodyToRestored := unifiedPrivacy.trans restorePrivacy
  have parametersAtBody := lifetime.older (Ty.productMany parameterTypes)
    (parameterBelow.weaken prefixProperties.1.next_le)
  have initialToPrefix := initialToParameter.trans prefixProperties.1
  have expectedAtBody : ∀ type ∈ expected, Safe protectedVars bodyResult.state type := by
    intro type member
    exact lifetime.older type ((expectedBelow type member).weaken initialToPrefix.next_le)
  have savedSubset : allocated.localBinders ⊆ bodyResult.state.localBinders := by
    apply (parameter_binders_subset parametersRun).trans
    apply List.Subset.trans (l₂ := prefixState.localBinders)
    · rw [prefix_binders prefixFacts]
      exact List.Subset.refl _
    · exact inferStatementsFuel_binders_subset bodyRun
  have restoredLive : LiveBindersSafe protectedVars restored := by
    intro binder member
    have before := lifetime.live binder (savedSubset member)
    exact before.transport bodyToRestored
  have resultToRestored := bodyProperties.1.trans (unifiedProgress.trans restoreProgress)
  have parametersToRestored := parametersToUnified.trans restoreProgress
  have initialToRestored := allocation.trans restoredProperties.1
  have recordPrivacy := recordExpressionWithExpected_private catalog restoredReady
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parametersToRestored.resolve_variablesBelow parameterBelow,
        resultToRestored.resolve_variablesBelow prefixProperties.2.2⟩)
    (fun type member => (expectedBelow type member).weaken initialToRestored.next_le)
    ((safe_function_iff _ _ _ _).mpr
      ⟨safe_resolved restoredReady (bodyToRestored _ parametersAtBody),
        safe_resolved restoredReady (bodyToRestored _ (lifetime.older resultType prefixProperties.2.2))⟩)
    (fun type member => bodyToRestored type (expectedAtBody type member)) restoredLive recorded
  have recordProperties := recordExpressionWithExpected_inferenceProperties restoredReady
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parametersToRestored.resolve_variablesBelow parameterBelow,
        resultToRestored.resolve_variablesBelow prefixProperties.2.2⟩)
    (fun type member => (expectedBelow type member).weaken initialToRestored.next_le) recorded
  have bodyToFinal := bodyToRestored.trans recordPrivacy.1
  have bodyRows : ∀ requirement ∈ restored.requirements,
      requirement ∉ event.readyState.requirements →
        PredicateSafe protectedVars restored requirement.predicate := by
    intro requirement member fresh type typeMember
    apply bodyToRestored
    apply lifetime.newRows requirement _ fresh type typeMember
    change requirement ∈ unifiedState.requirements at member
    simpa only [unify_requirements_eq unified] using member
  exact {
    createdAfter := Nat.le_trans initialToPrefix.next_le lifetime.createdAfter
    allocated := lifetime.allocated
    bound := fun q member => Nat.lt_of_lt_of_le (lifetime.bound q member)
      (Nat.le_trans unifiedProgress.next_le (Nat.le_trans restoreProgress.next_le recordProperties.1.next_le))
    transport := lifetime.transport.trans bodyToFinal
    live := recordPrivacy.2.2.1
    values := fun type member => (List.mem_singleton.mp member) ▸ recordPrivacy.2.1
    older := fun type below => bodyToFinal type (lifetime.older type (below.weaken initialToPrefix.next_le))
    newRows := new_requirements_trans bodyRows recordPrivacy.2.2.2 recordPrivacy.1 }

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
