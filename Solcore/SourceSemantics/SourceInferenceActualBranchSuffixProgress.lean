import Solcore.SourceSemantics.SourceInferenceActualExpressionSuffixProgress

/-! Actual branch, index and lambda continuations preserve the inference
substitution produced inside them. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness SourceInferenceSoundness.ProtectedVariables

theorem conditional_suffix_progress
    {fuel : Nat} {context : SourceInference.Context}
    {source condition thenBranch elseBranch : Syntax.Expr} {id : ExpressionId}
    {expected : Option Ty} {initial : State}
    {conditionResult thenResult elseResult result : InferredExpression × State}
    {unifiedState : State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (conditionRun : inferExprFuel fuel context condition (some .bool) initial = .ok conditionResult)
    (thenRun : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseRun : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (unified : unify elseResult.2 thenResult.1.type elseResult.1.type = .ok unifiedState)
    (recorded : recordExpressionWithExpected context source id
      (unifiedState.resolve thenResult.1.type)
      (.conditional conditionResult.1.id thenResult.1.id elseResult.1.id) [] expected unifiedState = .ok result) :
    conditionResult.2.InferenceProgress result.2 ∧
      thenResult.2.InferenceProgress result.2 ∧ elseResult.2.InferenceProgress result.2 := by
  have boolBelow : ∀ type ∈ (some Ty.bool : Option Ty),
      type.VariablesBelow initial.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact Ty.variablesBelow_constructor _ _
  have conditionProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical boolBelow conditionRun
  have thenProperties := inferExprFuel_inferenceProperties conditionProperties.2.1 catalog.formation catalog.canonical
    (fun type member => (expectedBelow type member).weaken conditionProperties.1.next_le) thenRun
  have elseProperties := inferExprFuel_inferenceProperties thenProperties.2.1 catalog.formation catalog.canonical
    (fun type member => (expectedBelow type member).weaken (conditionProperties.1.trans thenProperties.1).next_le) elseRun
  have thenBelow := thenProperties.2.2.weaken elseProperties.1.next_le
  have unifiedProgress := unify_inferenceProgress elseProperties.2.1.solved thenBelow elseProperties.2.2 unified
  have unifiedReady := unify_preserves_inferenceReady elseProperties.2.1 thenBelow elseProperties.2.2 unified
  have recordedProgress := (recordExpressionWithExpected_inferenceProperties unifiedReady
    (unifiedReady.solved.variablesBelow_apply (thenBelow.weaken unifiedProgress.next_le))
    (fun type member => (expectedBelow type member).weaken
      (conditionProperties.1.trans (thenProperties.1.trans (elseProperties.1.trans unifiedProgress))).next_le)
    recorded).1
  have afterElse := unifiedProgress.trans recordedProgress
  exact ⟨thenProperties.1.trans (elseProperties.1.trans afterElse),
    elseProperties.1.trans afterElse, afterElse⟩

theorem index_suffix_progress
    {fuel : Nat} {context : SourceInference.Context} {source key : Syntax.Expr}
    {id : ExpressionId} {expected : Option Ty}
    {baseResult keyResult : InferredExpression}
    {baseState keyState valueState mappingState indexState : State}
    {keyType valueType : Ty} {result : InferredExpression × State}
    (ready : baseState.InferenceReady) (catalog : LifetimeInferenceContext context)
    (baseBelow : baseResult.type.VariablesBelow baseState.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow baseState.inference.next)
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingRun : unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyRun : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (recorded : recordExpressionWithExpected context source id (indexState.resolve valueType)
      (.index baseResult.id keyResult.id) [] expected indexState = .ok result) :
    baseState.InferenceProgress result.2 ∧ indexState.InferenceProgress result.2 := by
  have keyProperties := fresh_eq_inferenceProperties ready keyFresh
  have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
  have baseBelow := baseBelow.weaken (keyProperties.1.trans valueProperties.1).next_le
  have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
  have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow mappingRun
  have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow mappingRun
  have expectedKey : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)
  have indexProperties := inferExprFuel_inferenceProperties mappingReady catalog.formation catalog.canonical expectedKey keyRun
  have valueBelow := valueProperties.2.2.weaken (mappingProgress.trans indexProperties.1).next_le
  have beforeRecord := keyProperties.1.trans (valueProperties.1.trans (mappingProgress.trans indexProperties.1))
  have recordedProgress := (recordExpressionWithExpected_inferenceProperties indexProperties.2.1
    (indexProperties.2.1.solved.variablesBelow_apply valueBelow)
    (fun type member => (expectedBelow type member).weaken beforeRecord.next_le) recorded).1
  exact ⟨beforeRecord.trans recordedProgress, recordedProgress⟩

theorem lambda_suffix_progress
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {annotation : Option Syntax.TypeExpr}
    {body : Syntax.Block} {expected : Option Ty} {initial : State}
    {boundParameters : List TypedBinder} {parameterTypes : List Ty} {parameterState : State}
    {resultType : Ty} {bodyState : State} {bodyResult : BlockResult}
    {unifiedState restoredState : State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (parametersRun : bindLambdaParameters context parameters.elements 0 []
      initial.allocateExpressionId.2 = .ok (boundParameters, parameterTypes, parameterState))
    (prefixFacts : LambdaPrefixFacts context expected annotation parameterTypes parameterState resultType bodyState)
    (bodyRun : inferStatementsFuel childFuel {context with loopDepth := 0}
      body.value resultType bodyState = .ok bodyResult)
    (unified : unify bodyResult.state bodyResult.type resultType = .ok unifiedState)
    (restored : restoredState = unifiedState.restoreLexicalScope initial.allocateExpressionId.2.lexicalScope)
    (recorded : recordExpressionWithExpected context source initial.allocateExpressionId.1
      (.function (restoredState.resolve (Ty.productMany parameterTypes)) (restoredState.resolve resultType))
      (.lambda boundParameters (restoredState.resolve resultType) bodyResult.statements)
      [] expected restoredState = .ok result) :
    bodyResult.state.InferenceProgress result.2 := by
  have allocation : initial.InferenceProgress initial.allocateExpressionId.2 :=
    .allocateExpressionId initial ready.solved
  have parametersProperties := bindLambdaParameters_inferenceProperties ready.allocateExpressionId parametersRun
  have parameterBelow := Ty.variablesBelow_productMany parametersProperties.2.2
  have initialToParameter := allocation.trans parametersProperties.1
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts parametersProperties.2.1
    parameterBelow (fun type member => (expectedBelow type member).weaken initialToParameter.next_le)
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) prefixProperties.2.1 catalog.formation catalog.canonical
    prefixProperties.2.2 bodyRun
  have unifiedProgress := unify_inferenceProgress bodyProperties.2.1.solved bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady bodyProperties.2.1 bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have parametersToUnified := prefixProperties.1.trans (bodyProperties.1.trans unifiedProgress)
  have restoredProperties := State.restoreLexicalScope_inferenceProperties ready.allocateExpressionId
    (parametersProperties.1.trans parametersToUnified)
  subst restoredState
  have restoreProgress : unifiedState.InferenceProgress
      (unifiedState.restoreLexicalScope initial.allocateExpressionId.2.lexicalScope) :=
    .restoreLexicalScope _ _ unifiedReady.solved
  have parametersToRestored := parametersToUnified.trans restoreProgress
  have bodyEntryToRestored := bodyProperties.1.trans (unifiedProgress.trans restoreProgress)
  have recordedProgress := (recordExpressionWithExpected_inferenceProperties restoredProperties.2
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parametersToRestored.resolve_variablesBelow parameterBelow,
        bodyEntryToRestored.resolve_variablesBelow prefixProperties.2.2⟩)
    (fun type member => (expectedBelow type member).weaken (allocation.trans restoredProperties.1).next_le)
    recorded).1
  exact unifiedProgress.trans (restoreProgress.trans recordedProgress)

end Solcore.SourceSemantics.SourceInferenceExecution
