import Solcore.SourceSemantics.SourceCompiledInitializedBlockResume
import Solcore.SourceSemantics.SourceInferenceLambdaOperationalPrefix

/-! An initializer inside a lambda keeps its quantifiers private through the
actual return unification, saved scope restoration and final expression fit.
The enclosing parameter and return types were allocated before the initializer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables Detail

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

theorem InitializedBlockResume.finish_lambda
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel childFuel : Nat} {selected : Selected compiled row fuel}
    {context : SourceInference.Context} {expression : Syntax.Expr} {source : Syntax.Statement}
    {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {annotation : Option Syntax.TypeExpr}
    {body : Syntax.Block} {expected : Option Ty} {initial : State}
    {boundParameters : List TypedBinder} {parameterTypes : List Ty} {parameterState : State}
    {resultType : Ty} {prefixState : State} {bodyResult : BlockResult}
    {unifiedState restoredState : State} {final : InferredExpression × State}
    (resume : InitializedBlockResume selected {context with loopDepth := 0}
      resultType prefixState bodyResult source)
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
    (unified : unify bodyResult.state bodyResult.type resultType = .ok unifiedState)
    (restoredEq : restoredState = unifiedState.restoreLexicalScope initial.allocateExpressionId.2.lexicalScope)
    (recorded : recordExpressionWithExpected context expression initial.allocateExpressionId.1
      (.function (restoredState.resolve (Ty.productMany parameterTypes)) (restoredState.resolve resultType))
      (.lambda boundParameters (restoredState.resolve resultType) bodyResult.statements)
      [] expected restoredState = .ok final) :
    SafeTransport resume.actual.receipt.binding.1.scheme.quantified resume.actual.receipt.ready final.2 ∧
      Safe resume.actual.receipt.binding.1.scheme.quantified final.2 final.1.type ∧
      LiveBindersSafe resume.actual.receipt.binding.1.scheme.quantified final.2 ∧
      ∀ requirement ∈ final.2.requirements, requirement ∉ resume.actual.receipt.ready.requirements →
        PredicateSafe resume.actual.receipt.binding.1.scheme.quantified final.2 requirement.predicate := by
  let protectedVars := resume.actual.receipt.binding.1.scheme.quantified
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
  have unifiedProgress := unify_inferenceProgress resume.ready.solved bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady resume.ready bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedPrivacy : SafeTransport protectedVars bodyResult.state unifiedState :=
    ProtectedVariables.unify resume.resultSafe resume.expectedSafe unified
  have parametersToUnified := prefixProperties.1.trans (bodyProperties.1.trans unifiedProgress)
  have allocatedToUnified := parametersProperties.1.trans parametersToUnified
  have restoredProperties := State.restoreLexicalScope_inferenceProperties ready.allocateExpressionId allocatedToUnified
  subst restoredState
  let restored := unifiedState.restoreLexicalScope allocated.lexicalScope
  have restoredReady : restored.InferenceReady := restoredProperties.2
  have restorePrivacy : SafeTransport protectedVars unifiedState restored := .of_substitution_eq rfl
  have restoreProgress : unifiedState.InferenceProgress restored := .restoreLexicalScope _ _ unifiedReady.solved
  have bodyToRestored := unifiedPrivacy.trans restorePrivacy
  have parametersAtBody := resume.olderSafe (Ty.productMany parameterTypes)
    (parameterBelow.weaken prefixProperties.1.next_le)
  have initialToPrefix := initialToParameter.trans prefixProperties.1
  have expectedAtBody : ∀ type ∈ expected, Safe protectedVars bodyResult.state type := by
    intro type member
    exact resume.olderSafe type ((expectedBelow type member).weaken initialToPrefix.next_le)
  have savedSubset : allocated.localBinders ⊆ bodyResult.state.localBinders := by
    apply (parameter_binders_subset parametersRun).trans
    apply List.Subset.trans (l₂ := prefixState.localBinders)
    · rw [prefix_binders prefixFacts]
      exact List.Subset.refl _
    · exact inferStatementsFuel_binders_subset bodyRun
  have restoredLive : LiveBindersSafe protectedVars restored := by
    intro binder member
    have before := resume.live binder (savedSubset member)
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
        safe_resolved restoredReady (bodyToRestored _ resume.expectedSafe)⟩)
    (fun type member => bodyToRestored type (expectedAtBody type member)) restoredLive recorded
  refine ⟨resume.transport.trans (bodyToRestored.trans recordPrivacy.1),
    recordPrivacy.2.1,recordPrivacy.2.2.1,?_⟩
  have bodyRows : ∀ requirement ∈ restored.requirements,
      requirement ∉ resume.actual.receipt.ready.requirements →
        PredicateSafe protectedVars restored requirement.predicate := by
    intro requirement member fresh type typeMember
    apply bodyToRestored
    apply resume.newRows requirement _ fresh type typeMember
    change requirement ∈ unifiedState.requirements at member
    simpa only [unify_requirements_eq unified] using member
  exact new_requirements_trans bodyRows recordPrivacy.2.2.2 recordPrivacy.1

private theorem parameter_owner
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State}
    {result : List TypedBinder × List Ty × State}
    (accepted : bindLambdaParameters context parameters index seen initial = .ok result) :
    result.2.2.owner = initial.owner := by
  induction parameters generalizing index seen initial result with
  | nil =>
    simp only [bindLambdaParameters, Except.ok.injEq] at accepted
    cases accepted
    rfl
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
        have tailOwner := ih _ _ _ (by assumption)
        exact tailOwner.trans rfl
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
          have tailOwner := ih _ _ _ (by assumption)
        exact tailOwner.trans rfl

private theorem prefix_owner
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty}
    {initial final : State} {resultType : Ty}
    (facts : LambdaPrefixFacts context expected annotation types initial resultType final) :
    final.owner = initial.owner := by
  cases facts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ fresh =>
    rw [← show initial.fresh.2 = final from congrArg Prod.snd fresh]
    rfl
  | expectedPartsAnnotated _ unified | expectedPartsInferred _ unified =>
    exact congrArg State.Header.owner (unify_state_header unified)

/-- Follow the actual lambda computation to a chosen initialized declaration
and back to the enclosing expression's actual result. No lambda body typing
or initializer barrier is needed. -/
theorem lambda_initializer_resume
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {context : SourceInference.Context} {expression : Syntax.Expr}
    {keyword : Syntax.SourceSpan} {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
    {annotation : Option Syntax.TypeExpr} {body : Syntax.Block}
    {expected : Option Ty} {initial : State} {final : InferredExpression × State}
    {index : Nat} {statement : Syntax.Statement}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (scope : CheckingScope selected context)
    (ready : initial.InferenceReady) (nodesBelow : initial.NodesBelowNextOccurrence)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (owner : initial.owner = (evidenceSource selected).owner)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      Safe binder.scheme.quantified initial type)
    (retained : final.2.nodes <+: selected.body.returned.nodes)
    (extension : selected.body.finalized.substitution.SemanticallyExtends final.2.inference.substitution)
    (form : expression.value = .lambda keyword parameters annotation body)
    (accepted : inferExprFuel (childFuel + 1) context expression expected initial = .ok final)
    (position : body.value[index]? = some statement)
    {name : Syntax.Identifier} {localAnnotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (statementForm : statement.value = .letDecl name localAnnotation (some initializer)) :
    ∃ actual : InitializerOccurrence selected statement,
      actual.inferenceContext = {context with loopDepth := 0} ∧
      SafeTransport actual.receipt.binding.1.scheme.quantified actual.receipt.ready final.2 ∧
      Safe actual.receipt.binding.1.scheme.quantified final.2 final.1.type ∧
      LiveBindersSafe actual.receipt.binding.1.scheme.quantified final.2 ∧
      (∀ q ∈ actual.receipt.binding.1.scheme.quantified,
        q.index < final.2.inference.next) ∧
      (∀ type, type.VariablesBelow initial.inference.next →
        Safe actual.receipt.binding.1.scheme.quantified final.2 type) ∧
      ∀ requirement ∈ final.2.requirements, requirement ∉ actual.receipt.ready.requirements →
        PredicateSafe actual.receipt.binding.1.scheme.quantified final.2 requirement.predicate := by
  obtain ⟨boundParameters, parameterTypes, parameterState, resultType, prefixState,
    bodyResult, unifiedState, restoredState, parametersRun, prefixFacts, bodyRun,
    unified, restoredEq, recorded⟩ :=
    inferExprFuel_success_lambda_facts form (Prod.eta initial.allocateExpressionId).symm accepted
  have formation := scope.formation checked
  have canonical := scope.functionsCanonical checked
  let allocated := initial.allocateExpressionId.2
  have allocation : initial.InferenceProgress allocated := .allocateExpressionId _ ready.solved
  have parameterProperties := bindLambdaParameters_inferenceProperties ready.allocateExpressionId parametersRun
  have parameterBelow := Ty.variablesBelow_productMany parameterProperties.2.2
  have initialToParameter := allocation.trans parameterProperties.1
  have expectedAtParameter := fun type member => (expectedBelow type member).weaken initialToParameter.next_le
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts parameterProperties.2.1
    parameterBelow expectedAtParameter
  have initialToPrefix := initialToParameter.trans prefixProperties.1
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) prefixProperties.2.1 formation canonical
    prefixProperties.2.2 bodyRun
  have unifiedProgress := unify_inferenceProgress bodyProperties.2.1.solved bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady bodyProperties.2.1 bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have restoreProgress : unifiedState.InferenceProgress restoredState := by
    rw [restoredEq]
    exact .restoreLexicalScope _ _ unifiedReady.solved
  have throughBody := parameterProperties.1.trans
    (prefixProperties.1.trans (bodyProperties.1.trans unifiedProgress))
  have restoredProperties : allocated.InferenceProgress restoredState ∧ restoredState.InferenceReady := by
    rw [restoredEq]
    exact State.restoreLexicalScope_inferenceProperties ready.allocateExpressionId throughBody
  have parameterToRestored := prefixProperties.1.trans
    (bodyProperties.1.trans (unifiedProgress.trans restoreProgress))
  have prefixToRestored := bodyProperties.1.trans (unifiedProgress.trans restoreProgress)
  have recordProperties := recordExpressionWithExpected_inferenceProperties restoredProperties.2
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parameterToRestored.resolve_variablesBelow parameterBelow,
        prefixToRestored.resolve_variablesBelow prefixProperties.2.2⟩)
    (fun type member => (expectedBelow type member).weaken (allocation.trans restoredProperties.1).next_le)
    recorded
  have bodyExtension := extension.trans
    ((unifiedProgress.trans restoreProgress).trans recordProperties.1).substitution_extends
  have bodyNodes : bodyResult.state.nodes <+: final.2.nodes := by
    have nodes := recordExpressionWithExpected_success_nodesPrefix recorded
    rw [restoredEq, State.restoreLexicalScope_nodes, (unify_occurrenceState_eq unified).1] at nodes
    exact nodes
  have parameterScope := bindLambdaParameters_operational ready.allocateExpressionId
    operational.allocateExpressionId parametersRun
  have parameterPrivacy : ∀ binder ∈ parameterState.localBinders,
      Safe binder.scheme.quantified parameterState (Ty.productMany parameterTypes) ∧
      (∀ type ∈ expected, Safe binder.scheme.quantified parameterState type) := by
    intro binder member
    rcases bindLambdaParameters_quantified_origin parametersRun binder member with old | mono
    · have privacy := bindLambdaParameters_private ready.allocateExpressionId
        (operational.quantifiersBelow binder old) (operational.allocateExpressionId.privacy binder old) parametersRun
      exact ⟨safe_productMany _ _ _ privacy.2.1,
        fun type present => privacy.1 type (expectedSafe binder old type present)⟩
    · rw [mono]
      simp [Safe, Avoids]
  have prefixScope := lambdaPrefixFacts_operational parameterProperties.2.1
    parameterScope parameterBelow
    (fun binder member => (parameterPrivacy binder member).1) expectedAtParameter
    (fun binder member => (parameterPrivacy binder member).2) prefixFacts
  have prefixNodes := lambdaPrefixFacts_nodesBelowNextOccurrence prefixFacts
    ((bindLambdaParameters_occurrenceBoundExtends parametersRun).nodesBelowNextOccurrence
      (State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodesBelow))
  have prefixOwner := (prefix_owner prefixFacts).trans ((parameter_owner parametersRun).trans owner)
  obtain ⟨resume⟩ := initialized_block_resume checked (scope.withLoopDepth 0)
    prefixProperties.2.1 prefixNodes ⟨prefixScope.1,prefixScope.2,prefixOwner⟩
    prefixProperties.2.2 (bodyNodes.trans retained) bodyExtension bodyRun position statementForm
  have finished := resume.finish_lambda ready (scope.catalog checked) formation canonical expectedBelow
    parametersRun prefixFacts bodyRun unified restoredEq recorded
  exact ⟨resume.actual,resume.context,finished.1,finished.2.1,finished.2.2.1,
    fun q member => Nat.lt_of_lt_of_le (resume.bound q member)
      (((unifiedProgress.trans restoreProgress).trans recordProperties.1).next_le),
    fun type below => finished.1 type (resume.olderAtReady type (below.weaken initialToPrefix.next_le)),
    finished.2.2.2⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
