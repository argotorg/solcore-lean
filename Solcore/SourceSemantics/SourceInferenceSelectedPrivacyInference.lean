import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyContracts
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyLocalLookup
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyLambdaContinuation
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyMatchContinuation
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyCallContinuation
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyForContinuation
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyMatchStatement

/-! Privacy through the actual mutually recursive source inference calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

private theorem allocateExpressionId_eq_inferenceProperties
    {initial next : State} {id : ExpressionId}
    (ready : initial.InferenceReady)
    (allocation : initial.allocateExpressionId = (id, next)) :
    initial.InferenceProgress next ∧ next.InferenceReady := by
  have progress :=
    State.InferenceProgress.allocateExpressionId initial ready.solved
  have nextReady := State.InferenceReady.allocateExpressionId ready
  rw [allocation] at progress nextReady
  exact ⟨progress, nextReady⟩

private theorem allocateExpressionId_privacy {protectedVars : List TypeVarId}
    {initial allocated : State} {id : ExpressionId}
    (live : LiveBindersSafe protectedVars initial)
    (allocation : initial.allocateExpressionId = (id, allocated)) :
    SafeTransport protectedVars initial allocated ∧ LiveBindersSafe protectedVars allocated ∧
      allocated.requirements = initial.requirements := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have transport : SafeTransport protectedVars initial allocated := by
    apply SafeTransport.of_substitution_eq
    rw [same]
    rfl
  exact ⟨transport, live.transport (by rw [same]; rfl) transport, by rw [same]; rfl⟩

private theorem allocateStatementId_eq_inferenceProperties
    {initial next : State} {id : StatementId}
    (ready : initial.InferenceReady)
    (allocation : initial.allocateStatementId = (id, next)) :
    initial.InferenceProgress next ∧ next.InferenceReady := by
  have progress :=
    State.InferenceProgress.allocateStatementId initial ready.solved
  have nextReady := State.InferenceReady.allocateStatementId ready
  rw [allocation] at progress nextReady
  exact ⟨progress, nextReady⟩

private theorem allocateStatementId_privacy {protectedVars : List TypeVarId}
    {initial allocated : State} {id : StatementId}
    (live : LiveBindersSafe protectedVars initial)
    (allocation : initial.allocateStatementId = (id, allocated)) :
    SafeTransport protectedVars initial allocated ∧ LiveBindersSafe protectedVars allocated ∧
      allocated.requirements = initial.requirements := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  have transport : SafeTransport protectedVars initial allocated := by
    apply SafeTransport.of_substitution_eq
    rw [same]
    rfl
  exact ⟨transport, live.transport (by rw [same]; rfl) transport, by rw [same]; rfl⟩

private theorem generalize_binding_private {protectedVars : List TypeVarId}
    {before state : State} {type : Ty} (name : String) (span : Option Syntax.SourceSpan)
    (beforeWF : before.RequirementsWellFormed) (wellFormed : state.RequirementsWellFormed)
    (ready : state.InferenceReady) (typeSafe : Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (newRows : ∀ row ∈ state.requirements, row ∉ before.requirements → PredicateSafe protectedVars state row.predicate) :
    let locals := state.binderEnvironment.apply state.inference.substitution
    let generalized := Detail.generalizeValue state locals before.nextRequirement (state.resolve type)
    let binding := (state.withLocals locals).allocateBinder name generalized.scheme span false generalized.requirements
    SafeTransport protectedVars state binding.2 ∧ LiveBindersSafe protectedVars binding.2 ∧
      binding.2.requirements = state.requirements := by
  dsimp only
  let locals := state.binderEnvironment.apply state.inference.substitution
  have transport : SafeTransport protectedVars state (state.withLocals locals) := .of_substitution_eq rfl
  have localLive := live.transport (after := state.withLocals locals) rfl transport
  have allocated := allocate_generalized_private (state := state.withLocals locals) (before := before)
    locals name span false beforeWF wellFormed (State.InferenceReady.withLocals locals ready)
    (transport _ (safe_resolved ready typeSafe)) localLive newRows
  exact ⟨transport.trans allocated.1, allocated.2, rfl⟩

private theorem recordNode_private {protectedVars : List TypeVarId} {state : State}
    (node : Node) (live : LiveBindersSafe protectedVars state) :
    SafeTransport protectedVars state (state.recordNode node) ∧
      LiveBindersSafe protectedVars (state.recordNode node) ∧
      (state.recordNode node).requirements = state.requirements :=
  ⟨.of_substitution_eq rfl, live.transport rfl (.of_substitution_eq rfl), rfl⟩

private theorem builtinFunction_type_closed (function : BuiltinFunctionId) :
    function.type.VariablesBelow 0 := by
  unfold BuiltinFunctionId.type
  apply (Ty.variablesBelow_function_iff _ _ _).mpr
  constructor
  · apply Ty.variablesBelow_productMany
    cases function <;> simp [BuiltinFunctionId.parameterTypes, Ty.integer, Ty.word]
  · cases function <;> simp [BuiltinFunctionId.returnType, Ty.integer, Ty.word, Ty.bool]

private theorem functionCandidates_scheme_body_variablesBelow
    {context : SourceInference.Context} {candidates : List ProgramFunctionSignature}
    (validated : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (subset : candidates ⊆ context.signatures.functions)
    (next : Nat) :
    ∀ signature ∈ candidates,
      signature.scheme.body.VariablesBelow next := by
  intro signature member
  have catalogMember := subset member
  exact validated.function_scheme_body_variablesBelow catalogMember
    (canonical signature catalogMember) next

private theorem unify_requirements {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) :
    result.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

private theorem new_rows_of_eq {protectedVars : List TypeVarId} {before after : State}
    (same : after.requirements = before.requirements) :
    ∀ row ∈ after.requirements, row ∉ before.requirements → PredicateSafe protectedVars after row.predicate := by
  intro row member fresh
  exact False.elim (fresh (same ▸ member))

set_option maxHeartbeats 2000000 in
private theorem inferFuel_privacy_internal (protectedVars : List TypeVarId) :
    (∀ fuel context expression expected state,
      InferExprFuelPrivacy protectedVars fuel context expression expected state) ∧
    (∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelPrivacy protectedVars fuel context source id
        instantiation arguments expected state) ∧
    (∀ fuel context sources expected state,
      InferConstructorArgumentsFuelPrivacy protectedVars fuel context sources
        expected state) ∧
    (∀ fuel context statements expectedReturn state,
      InferStatementsFuelPrivacy protectedVars fuel context statements
        expectedReturn state) ∧
    (∀ fuel context statement expectedReturn state,
      InferStatementFuelPrivacy protectedVars fuel context statement
        expectedReturn state) ∧
    (∀ fuel context items state,
      InferForItemsFuelPrivacy protectedVars fuel context items state) ∧
    (∀ fuel context item state,
      InferForItemFuelPrivacy protectedVars fuel context item state) ∧
    (∀ fuel context target state,
      InferPlaceFuelPrivacy protectedVars fuel context target state) ∧
    (∀ fuel context target operator value state,
      InferAssignedValueFuelPrivacy protectedVars fuel context target operator
        value state) ∧
    (∀ fuel context expressions state,
      InferExprsFuelPrivacy protectedVars fuel context expressions state) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      InferMatchCasesFuelPrivacy protectedVars fuel context scrutineeType
        expectedReturn outerScope cases state) := by
  apply inferExprFuel.mutual_induct
    (motive1 := InferExprFuelPrivacy protectedVars)
    (motive2 := InferConstructorApplicationFuelPrivacy protectedVars)
    (motive3 := InferConstructorArgumentsFuelPrivacy protectedVars)
    (motive4 := InferStatementsFuelPrivacy protectedVars)
    (motive5 := InferStatementFuelPrivacy protectedVars)
    (motive6 := InferForItemsFuelPrivacy protectedVars)
    (motive7 := InferForItemFuelPrivacy protectedVars)
    (motive8 := InferPlaceFuelPrivacy protectedVars)
    (motive9 := InferAssignedValueFuelPrivacy protectedVars)
    (motive10 := InferExprsFuelPrivacy protectedVars)
    (motive11 := InferMatchCasesFuelPrivacy protectedVars)
  case case1 =>
    simp [InferExprFuelPrivacy, inferExprFuel]
  case case2 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelPrivacy
    intro ready _ bound live catalog _ _ expectedBelow expectedSafe result success
    let type : Ty := allocated.fresh.1
    let freshState : State := allocated.fresh.2
    let metavariable : TypeVarId := ⟨allocated.inference.next⟩
    let addition := freshState.addRequirementWithId
      (ProgramSignatures.builtinIntPredicate type)
    let literalState : State := {
      addition.2 with integerLiterals := addition.2.integerLiterals ++ [{
        metavariable
        expression := id
        requirement := addition.1
      }]
    }
    have allocationProgress : initial.InferenceProgress allocated := by
      have progress :=
        State.InferenceProgress.allocateExpressionId initial ready.solved
      rw [allocationEq] at progress
      exact progress
    have allocatedReady : allocated.InferenceReady := by
      have nextReady := State.InferenceReady.allocateExpressionId ready
      rw [allocationEq] at nextReady
      exact nextReady
    have freshProgress : allocated.InferenceProgress freshState := by
      simpa only [freshState] using
        State.InferenceProgress.fresh allocated allocatedReady.solved
    have freshReady : freshState.InferenceReady := by
      simpa only [freshState] using State.InferenceReady.fresh allocatedReady
    have typeBelowFresh : type.VariablesBelow
        freshState.inference.next := by
      change Ty.VariablesBelow (allocated.inference.next + 1)
        (.variable ⟨allocated.inference.next⟩)
      exact (Ty.variablesBelow_variable_iff _ _).2 (Nat.lt_succ_self _)
    have additionProgress : freshState.InferenceProgress addition.2 := by
      simpa only [addition] using
        State.InferenceProgress.addRequirementWithId freshState
          (ProgramSignatures.builtinIntPredicate type) freshReady.solved
    have additionReady : addition.2.InferenceReady := by
      simpa only [addition] using
        State.InferenceReady.addRequirementWithId
          (ProgramSignatures.builtinIntPredicate type) freshReady
    have metadataProgress : addition.2.InferenceProgress literalState := by
      exact State.InferenceProgress.of_inference_eq additionReady.solved rfl
    have metadataReady : literalState.InferenceReady :=
      State.InferenceReady.of_progress_of_binderEnvironment_eq additionReady
        metadataProgress rfl
    have prefixProgress : initial.InferenceProgress literalState :=
      allocationProgress.trans
        (freshProgress.trans (additionProgress.trans metadataProgress))
    have typeAtLiteral : type.VariablesBelow
        literalState.inference.next :=
      typeBelowFresh.weaken
        (additionProgress.trans metadataProgress).next_le
    have expectedAtLiteral : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow literalState.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken prefixProgress.next_le
    have recordSuccess :
        recordExpressionWithExpected context expression id type
          (.integerLiteral (.decimal spelling) {
            rawValue
            targetType := type
            requirement := addition.1
          }) [addition.1] expected literalState = .ok result := by
      unfold inferExprFuel at success
      simp only [allocationEq, expressionEq, literalEq, numericEq, bind,
        Except.bind, pure, Pure.pure, Except.pure] at success
      simpa only [type, freshState, metavariable, addition, literalState,
        State.fresh, TypeSystem.InferState.fresh, Prod.eta] using success
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have initialTransport : SafeTransport protectedVars initial literalState := by
      apply SafeTransport.of_substitution_eq
      change allocated.inference.substitution = initial.inference.substitution
      rw [allocatedEq]
      rfl
    have typeSafe : Safe protectedVars literalState type :=
      (SafeTransport.of_substitution_eq rfl : SafeTransport protectedVars freshState literalState)
        _ (fresh_type allocatedReady boundAllocated)
    have binders : literalState.localBinders = initial.localBinders := by
      change allocated.localBinders = initial.localBinders
      rw [allocatedEq]
      rfl
    have newRows : ∀ row ∈ literalState.requirements, row ∉ initial.requirements →
        PredicateSafe protectedVars literalState row.predicate := by
      intro row member fresh
      change row ∈ allocated.requirements ++
        [{id := addition.1, predicate := ProgramSignatures.builtinIntPredicate type}] at member
      have sameRows : allocated.requirements = initial.requirements := by rw [allocatedEq]; rfl
      rw [sameRows] at member
      rcases List.mem_append.mp member with old | introduced
      · exact False.elim (fresh old)
      · cases List.mem_singleton.mp introduced
        intro predicateType typeMember
        have same : predicateType = type := by simpa [ProgramSignatures.builtinIntPredicate] using typeMember
        exact same ▸ typeSafe
    have recorded := recordExpressionWithExpected_private catalog metadataReady typeAtLiteral
      expectedAtLiteral typeSafe (fun expectedType member => initialTransport _ (expectedSafe _ member))
      (live.transport binders initialTransport) recordSuccess
    exact ⟨initialTransport.trans recorded.1, recorded.2.1, recorded.2.2.1,
      new_requirements_trans newRows recorded.2.2.2 recorded.1⟩
  case case3 =>
    simp_all [InferExprFuelPrivacy, inferExprFuel, bind,
      Except.bind]
  case case4 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelPrivacy
    intro ready _ bound live catalog _ _ expectedBelow expectedSafe result success
    let type : Ty := allocated.fresh.1
    let freshState : State := allocated.fresh.2
    let metavariable : TypeVarId := ⟨allocated.inference.next⟩
    let addition := freshState.addRequirementWithId
      (ProgramSignatures.builtinIntPredicate type)
    let literalState : State := {
      addition.2 with integerLiterals := addition.2.integerLiterals ++ [{
        metavariable
        expression := id
        requirement := addition.1
      }]
    }
    have allocationProgress : initial.InferenceProgress allocated := by
      have progress :=
        State.InferenceProgress.allocateExpressionId initial ready.solved
      rw [allocationEq] at progress
      exact progress
    have allocatedReady : allocated.InferenceReady := by
      have nextReady := State.InferenceReady.allocateExpressionId ready
      rw [allocationEq] at nextReady
      exact nextReady
    have freshProgress : allocated.InferenceProgress freshState := by
      simpa only [freshState] using
        State.InferenceProgress.fresh allocated allocatedReady.solved
    have freshReady : freshState.InferenceReady := by
      simpa only [freshState] using State.InferenceReady.fresh allocatedReady
    have typeBelowFresh : type.VariablesBelow
        freshState.inference.next := by
      change Ty.VariablesBelow (allocated.inference.next + 1)
        (.variable ⟨allocated.inference.next⟩)
      exact (Ty.variablesBelow_variable_iff _ _).2 (Nat.lt_succ_self _)
    have additionProgress : freshState.InferenceProgress addition.2 := by
      simpa only [addition] using
        State.InferenceProgress.addRequirementWithId freshState
          (ProgramSignatures.builtinIntPredicate type) freshReady.solved
    have additionReady : addition.2.InferenceReady := by
      simpa only [addition] using
        State.InferenceReady.addRequirementWithId
          (ProgramSignatures.builtinIntPredicate type) freshReady
    have metadataProgress : addition.2.InferenceProgress literalState := by
      exact State.InferenceProgress.of_inference_eq additionReady.solved rfl
    have metadataReady : literalState.InferenceReady :=
      State.InferenceReady.of_progress_of_binderEnvironment_eq additionReady
        metadataProgress rfl
    have prefixProgress : initial.InferenceProgress literalState :=
      allocationProgress.trans
        (freshProgress.trans (additionProgress.trans metadataProgress))
    have typeAtLiteral : type.VariablesBelow
        literalState.inference.next :=
      typeBelowFresh.weaken
        (additionProgress.trans metadataProgress).next_le
    have expectedAtLiteral : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow literalState.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken prefixProgress.next_le
    have recordSuccess :
        recordExpressionWithExpected context expression id type
          (.integerLiteral (.hexadecimal spelling) {
            rawValue
            targetType := type
            requirement := addition.1
          }) [addition.1] expected literalState = .ok result := by
      unfold inferExprFuel at success
      simp only [allocationEq, expressionEq, literalEq, numericEq, bind,
        Except.bind, pure, Pure.pure, Except.pure] at success
      simpa only [type, freshState, metavariable, addition, literalState,
        State.fresh, TypeSystem.InferState.fresh, Prod.eta] using success
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have initialTransport : SafeTransport protectedVars initial literalState := by
      apply SafeTransport.of_substitution_eq
      change allocated.inference.substitution = initial.inference.substitution
      rw [allocatedEq]
      rfl
    have typeSafe : Safe protectedVars literalState type :=
      (SafeTransport.of_substitution_eq rfl : SafeTransport protectedVars freshState literalState)
        _ (fresh_type allocatedReady boundAllocated)
    have binders : literalState.localBinders = initial.localBinders := by
      change allocated.localBinders = initial.localBinders
      rw [allocatedEq]
      rfl
    have newRows : ∀ row ∈ literalState.requirements, row ∉ initial.requirements →
        PredicateSafe protectedVars literalState row.predicate := by
      intro row member fresh
      change row ∈ allocated.requirements ++
        [{id := addition.1, predicate := ProgramSignatures.builtinIntPredicate type}] at member
      have sameRows : allocated.requirements = initial.requirements := by rw [allocatedEq]; rfl
      rw [sameRows] at member
      rcases List.mem_append.mp member with old | introduced
      · exact False.elim (fresh old)
      · cases List.mem_singleton.mp introduced
        intro predicateType typeMember
        have same : predicateType = type := by simpa [ProgramSignatures.builtinIntPredicate] using typeMember
        exact same ▸ typeSafe
    have recorded := recordExpressionWithExpected_private catalog metadataReady typeAtLiteral
      expectedAtLiteral typeSafe (fun expectedType member => initialTransport _ (expectedSafe _ member))
      (live.transport binders initialTransport) recordSuccess
    exact ⟨initialTransport.trans recorded.1, recorded.2.1, recorded.2.2.1,
      new_requirements_trans newRows recorded.2.2.2 recorded.1⟩
  case case5 =>
    simp_all [InferExprFuelPrivacy, inferExprFuel, bind,
      Except.bind]
  case case6 =>
    simp_all [InferExprFuelPrivacy, inferExprFuel]

  case case7 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq binder lookupEq localSchemeInstantiationStart
      instantiated inference advanced predicates requirements recorded requirementsEq
    unfold InferExprFuelPrivacy
    intro ready _ bound live catalog _ _ expectedBelow expectedSafe result success
    exact UnrestrictedLocalLookup.inferExprFuel_local_private catalog expressionEq allocationEq lookupEq
      success ready bound live expectedBelow expectedSafe
  case case8 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone isBoolean
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    have expectedAtAllocated : ∀ expectedType ∈ expected, expectedType.VariablesBelow allocated.inference.next :=
      fun expectedType member => (expectedBelow expectedType member).weaken allocationProperties.1.next_le
    have expectedSafeAtAllocated : ∀ expectedType ∈ expected, Safe protectedVars allocated expectedType :=
      fun expectedType member => allocationPrivacy.1 _ (expectedSafe _ member)
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, lookupNone, isBoolean, if_true]
      at success
    have recorded := recordExpressionWithExpected_private catalog allocationProperties.2
      (Ty.variablesBelow_constructor _ _) expectedAtAllocated
      (safe_closed _ _ (Ty.variablesBelow_constructor _ _)) expectedSafeAtAllocated
      allocationPrivacy.2.1 success
    refine ⟨allocationPrivacy.1.trans recorded.1, recorded.2.1, recorded.2.2.1, ?_⟩
    intro row member fresh
    exact recorded.2.2.2 row member (by simpa only [allocationPrivacy.2.2] using fresh)
  case case9 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone notBool
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties := allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    have expectedAtAllocated : ∀ expectedType ∈ expected, expectedType.VariablesBelow allocated.inference.next :=
      fun expectedType member => (expectedBelow expectedType member).weaken allocationProperties.1.next_le
    have expectedSafeAtAllocated : ∀ expectedType ∈ expected, Safe protectedVars allocated expectedType :=
      fun expectedType member => allocationPrivacy.1 _ (expectedSafe _ member)
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, lookupNone, notBool, bind,
      Except.bind] at success
    cases functionsResult : functionsNamed context name.value with
    | error error =>
        simp [functionsResult] at success
    | ok candidates =>
        simp only [functionsResult] at success
        cases candidates with
        | nil =>
            cases builtinResult : builtinFunctionNamed? name.value with
            | none => simp [builtinResult] at success
            | some function =>
                simp only [builtinResult] at success
                have recorded := recordExpressionWithExpected_private catalog allocationProperties.2
                  ((builtinFunction_type_closed function).weaken (Nat.zero_le _)) expectedAtAllocated
                  (safe_closed _ _ (builtinFunction_type_closed function)) expectedSafeAtAllocated
                  allocationPrivacy.2.1 success
                refine ⟨allocationPrivacy.1.trans recorded.1, recorded.2.1, recorded.2.2.1, ?_⟩
                intro row member fresh
                exact recorded.2.2.2 row member (by simpa only [allocationPrivacy.2.2] using fresh)
        | cons signature rest =>
            cases rest with
            | nil =>
                have catalogMember :
                    signature ∈ context.signatures.functions :=
                  functionsNamed_success_subset_catalog functionsResult
                    (by simp)
                have recorded := declaration_reference_private catalog catalogMember allocationProperties.2
                  boundAllocated expectedAtAllocated expectedSafeAtAllocated allocationPrivacy.2.1 success
                refine ⟨allocationPrivacy.1.trans recorded.1, recorded.2.1, recorded.2.2.1, ?_⟩
                intro row member fresh
                exact recorded.2.2.2 row member (by simpa only [allocationPrivacy.2.2] using fresh)
            | cons second tail => simp at success
  case case10 =>
    intros context expression expected initial fuel id allocated allocationEq
      inner expressionEq innerInduction
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    have expectedAtAllocated : ∀ expectedType ∈ expected, expectedType.VariablesBelow allocated.inference.next :=
      fun expectedType member => (expectedBelow expectedType member).weaken allocationProperties.1.next_le
    have expectedSafeAtAllocated : ∀ expectedType ∈ expected, Safe protectedVars allocated expectedType :=
      fun expectedType member => allocationPrivacy.1 _ (expectedSafe _ member)
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases innerResult : inferExprFuel fuel context inner expected allocated with
    | error error =>
        simp [innerResult] at success
    | ok innerPair =>
        rcases innerPair with ⟨inferred, innerState⟩
        simp only [innerResult] at success
        have innerPrivacy := innerInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          catalog validated canonical expectedAtAllocated expectedSafeAtAllocated (inferred, innerState) innerResult
        have innerProperties := inferExprFuel_inferenceProperties allocationProperties.2
          validated canonical expectedAtAllocated innerResult
        have prefixProgress := allocationProperties.1.trans innerProperties.1
        have beforeFit := allocationPrivacy.1.trans innerPrivacy.1
        have recorded := recordExpressionWithExpected_private catalog innerProperties.2.1 innerProperties.2.2
          (fun type member => (expectedBelow type member).weaken prefixProgress.next_le)
          innerPrivacy.2.1 (fun type member => beforeFit _ (expectedSafe _ member)) innerPrivacy.2.2.1 success
        refine ⟨beforeFit.trans recorded.1, recorded.2.1, recorded.2.2.1, ?_⟩
        intro row member fresh
        exact new_requirements_trans innerPrivacy.2.2.2 recorded.2.2.2 recorded.1 row member
          (by simpa only [allocationPrivacy.2.2] using fresh)
  case case11 =>
    intros context expression expected initial fuel id allocated allocationEq
      elements expressionEq elementsInduction
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    have expectedAtAllocated : ∀ expectedType ∈ expected, expectedType.VariablesBelow allocated.inference.next :=
      fun expectedType member => (expectedBelow expectedType member).weaken allocationProperties.1.next_le
    have expectedSafeAtAllocated : ∀ expectedType ∈ expected, Safe protectedVars allocated expectedType :=
      fun expectedType member => allocationPrivacy.1 _ (expectedSafe _ member)
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases elementsResult : inferExprsFuel fuel context elements.elements
        allocated with
    | error error =>
        simp [elementsResult] at success
    | ok elementsPair =>
        rcases elementsPair with ⟨inferredElements, elementsState⟩
        simp only [elementsResult] at success
        have elementsPrivacy := elementsInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          catalog validated canonical (inferredElements, elementsState) elementsResult
        have elementsProperties := inferExprsFuel_inferenceProperties allocationProperties.2
          validated canonical elementsResult
        have tupleTypeBelow :
            (Ty.productMany (inferredElements.map (·.type))).VariablesBelow
              elementsState.inference.next :=
          Ty.variablesBelow_productMany (by
            intro type member
            simp only [List.mem_map] at member
            obtain ⟨element, elementMember, rfl⟩ := member
            exact elementsProperties.2.2 element elementMember)
        have prefixProgress :=
          allocationProperties.1.trans elementsProperties.1
        have beforeFit := allocationPrivacy.1.trans elementsPrivacy.1
        have tupleSafe : Safe protectedVars elementsState (Ty.productMany (inferredElements.map (·.type))) := by
          apply safe_productMany
          intro type member
          obtain ⟨element, elementMember, rfl⟩ := List.mem_map.mp member
          exact elementsPrivacy.2.1 element elementMember
        have recorded := recordExpressionWithExpected_private catalog elementsProperties.2.1 tupleTypeBelow
          (fun type member => (expectedBelow type member).weaken prefixProgress.next_le)
          tupleSafe (fun type member => beforeFit _ (expectedSafe _ member)) elementsPrivacy.2.2.1 success
        refine ⟨beforeFit.trans recorded.1, recorded.2.1, recorded.2.2.1, ?_⟩
        intro row member fresh
        exact new_requirements_trans elementsPrivacy.2.2.2 recorded.2.2.2 recorded.1 row member
          (by simpa only [allocationPrivacy.2.2] using fresh)

  case case12 =>
    intros context expression expected initial fuel id allocated allocationEq
      operator operand expressionEq operandInduction
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases operandResult : inferExprFuel fuel context operand none allocated with
    | error error =>
        simp [operandResult] at success
    | ok operandPair =>
        rcases operandPair with ⟨inferredOperand, operandState⟩
        simp only [operandResult] at success
        have operandPrivacy := operandInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          catalog validated canonical (by simp) (by simp) (inferredOperand, operandState) operandResult
        have operandProperties := inferExprFuel_inferenceProperties allocationProperties.2 validated canonical (by simp) operandResult
        have beforeOperand := allocationPrivacy.1.trans operandPrivacy.1
        have expectedSafeAtOperand : ∀ type ∈ expected, Safe protectedVars operandState type :=
          fun type member => beforeOperand _ (expectedSafe _ member)
        have prefixProgress :=
          allocationProperties.1.trans operandProperties.1
        have expectedAtOperand : ∀ expectedType ∈ expected,
            expectedType.VariablesBelow operandState.inference.next := by
          intro expectedType member
          exact (expectedBelow expectedType member).weaken
            prefixProgress.next_le
        let integerLiterals := relevantIntegerLiterals operandState
          allocated.integerLiterals.length [inferredOperand]
        have finishInferred (inferred : OperatorInferenceResult)
            (inferenceSuccess : inferUnaryOperator context operator.value
              inferredOperand.type expected integerLiterals operandState =
                .ok inferred)
            (recordSuccess : recordExpressionWithExpected context expression id
              inferred.type (.unary operator.value inferredOperand.id)
              inferred.requirements expected inferred.state = .ok result) :
            SafeTransport protectedVars initial result.2 ∧ Safe protectedVars result.2 result.1.type ∧
              LiveBindersSafe protectedVars result.2 ∧
              ∀ row ∈ result.2.requirements, row ∉ initial.requirements → PredicateSafe protectedVars result.2 row.predicate := by
          have inferredPrivacy := inferUnaryOperator_private catalog operandProperties.2.1 operandProperties.2.2 expectedAtOperand
            operandPrivacy.2.1 expectedSafeAtOperand operandPrivacy.2.2.1 inferenceSuccess
          have inferredProperties := inferUnaryOperator_inferenceProperties
            operandProperties.2.1 operandProperties.2.2 expectedAtOperand
            inferenceSuccess
          have expectedAtInferred : ∀ expectedType ∈ expected,
              expectedType.VariablesBelow inferred.state.inference.next := by
            intro expectedType member
            exact (expectedAtOperand expectedType member).weaken
              inferredProperties.1.next_le
          have recorded := recordExpressionWithExpected_private catalog inferredProperties.2.1 inferredProperties.2.2
            expectedAtInferred inferredPrivacy.2.1 (fun type member => inferredPrivacy.1 _ (expectedSafeAtOperand _ member))
            inferredPrivacy.2.2.1 recordSuccess
          have tailTransport := inferredPrivacy.1.trans recorded.1
          refine ⟨beforeOperand.trans tailTransport, recorded.2.1, recorded.2.2.1, ?_⟩
          intro row member fresh
          exact new_requirements_trans operandPrivacy.2.2.2
            (new_requirements_trans inferredPrivacy.2.2.2 recorded.2.2.2 recorded.1)
            tailTransport row member (by simpa only [allocationPrivacy.2.2] using fresh)
        cases dispatchEq : unaryOperatorDispatch operator.value with
        | traitMethod traitName methodName =>
            simp only [dispatchEq] at success
            cases inferredResult : inferUnaryOperator context operator.value
                inferredOperand.type expected integerLiterals operandState with
            | error error =>
                simp [integerLiterals, inferredResult]
                  at success
            | ok inferred =>
                simp only [integerLiterals, inferredResult] at success
                exact finishInferred inferred inferredResult success
        | function name =>
            simp only [dispatchEq] at success
            cases functionsResult : functionsNamed context name with
            | error error =>
                simp [functionsResult] at success
            | ok candidates =>
                simp only [functionsResult] at success
                cases candidates with
                | nil =>
                    cases inferredResult : inferUnaryOperator context
                        operator.value inferredOperand.type expected
                        integerLiterals operandState with
                    | error error =>
                        simp [integerLiterals, inferredResult] at success
                    | ok inferred =>
                        simp only [integerLiterals, inferredResult] at success
                        exact finishInferred inferred inferredResult success
                | cons candidate rest =>
                    cases selectionResult : selectFunctionCandidateFrom context
                        name (candidate :: rest) [inferredOperand]
                        integerLiterals id expected operandState with
                    | error error =>
                        simp [integerLiterals, selectionResult] at success
                    | ok attempt =>
                        simp only [integerLiterals, selectionResult, pure, Pure.pure, Except.pure] at success
                        let callee : Syntax.Expr := {
                          span := operator.span
                          value := .identifier {
                            span := operator.span
                            value := name
                          }
                        }
                        change Except.ok (recordSelectedCall expression callee
                          name [inferredOperand] attempt) = Except.ok result
                            at success
                        injection success with resultEq
                        have selectedPrivacy := selectFunctionCandidateFrom_private catalog
                          (functionsNamed_success_subset_catalog functionsResult) operandProperties.2.1
                          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) prefixProgress.next_le)
                          (by intro argument member; have same := List.mem_singleton.mp member; subst argument; exact operandProperties.2.2)
                          expectedAtOperand
                          (by intro argument member; have same := List.mem_singleton.mp member; subst argument; exact operandPrivacy.2.1)
                          expectedSafeAtOperand operandPrivacy.2.2.1 selectionResult
                        have recorded := recordSelectedCall_private expression callee name [inferredOperand] attempt
                          selectedPrivacy.2.1 selectedPrivacy.2.2.1
                        rw [← resultEq]
                        have tailTransport := selectedPrivacy.1.trans recorded.1
                        refine ⟨beforeOperand.trans tailTransport, recorded.2.1, recorded.2.2.1, ?_⟩
                        intro row member fresh
                        exact new_requirements_trans operandPrivacy.2.2.2
                          (new_requirements_trans selectedPrivacy.2.2.2 (new_rows_of_eq recorded.2.2.2) recorded.1)
                          tailTransport row member (by simpa only [allocationPrivacy.2.2] using fresh)

  case case13 =>
    intros context expression expected initial fuel id allocated allocationEq
      left operator right expressionEq leftInduction rightInduction
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases leftResult : inferExprFuel fuel context left none allocated with
    | error error =>
        simp [leftResult] at success
    | ok leftPair =>
        rcases leftPair with ⟨inferredLeft, leftState⟩
        simp only [leftResult] at success
        have leftPrivacy := leftInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          catalog validated canonical (by simp) (by simp) (inferredLeft, leftState) leftResult
        have leftProperties := inferExprFuel_inferenceProperties allocationProperties.2 validated canonical (by simp) leftResult
        cases rightResult : inferExprFuel fuel context right none leftState with
        | error error =>
            simp [rightResult] at success
        | ok rightPair =>
            rcases rightPair with ⟨inferredRight, rightState⟩
            simp only [rightResult] at success
            have rightPrivacy := rightInduction leftState leftProperties.2.1
              ((inferExprFuel_direct_progress leftResult).wellFormed wfAllocated)
              (fun metavariable member => Nat.lt_of_lt_of_le (boundAllocated metavariable member) leftProperties.1.next_le)
              leftPrivacy.2.2.1 catalog validated canonical (by simp) (by simp) (inferredRight, rightState) rightResult
            have rightProperties := inferExprFuel_inferenceProperties leftProperties.2.1 validated canonical (by simp) rightResult
            have beforeRight := allocationPrivacy.1.trans (leftPrivacy.1.trans rightPrivacy.1)
            have beforeRightRows := new_requirements_trans leftPrivacy.2.2.2 rightPrivacy.2.2.2 rightPrivacy.1
            have expectedSafeAtRight : ∀ type ∈ expected, Safe protectedVars rightState type :=
              fun type member => beforeRight _ (expectedSafe _ member)
            have leftSafeAtRight := rightPrivacy.1 _ leftPrivacy.2.1
            have argumentsSafe : ∀ argument ∈ [inferredLeft, inferredRight], Safe protectedVars rightState argument.type := by
              intro argument member
              rcases List.mem_cons.mp member with rfl | member
              · exact leftSafeAtRight
              · have same := List.mem_singleton.mp member
                subst argument
                exact rightPrivacy.2.1
            have leftAtRight : inferredLeft.type.VariablesBelow
                rightState.inference.next :=
              leftProperties.2.2.weaken rightProperties.1.next_le
            have argumentsBelow :
                ∀ argument ∈ [inferredLeft, inferredRight],
                  argument.type.VariablesBelow rightState.inference.next := by
              intro argument member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact leftAtRight
              · rcases member with rfl | member
                · exact rightProperties.2.2
                · simp at member
            have prefixProgress := allocationProperties.1.trans
              (leftProperties.1.trans rightProperties.1)
            have expectedAtRight : ∀ expectedType ∈ expected,
                expectedType.VariablesBelow rightState.inference.next := by
              intro expectedType member
              exact (expectedBelow expectedType member).weaken
                prefixProgress.next_le
            let integerLiterals := relevantIntegerLiterals rightState
              allocated.integerLiterals.length [inferredLeft, inferredRight]
            have finishInferred (inferred : OperatorInferenceResult)
                (inferenceSuccess : inferBinaryOperator context operator.value
                  inferredLeft.type inferredRight.type expected integerLiterals
                    rightState = .ok inferred)
                (recordSuccess : recordExpressionWithExpected context
                  expression id inferred.type
                  (.binary inferredLeft.id operator.value inferredRight.id)
                  inferred.requirements expected inferred.state = .ok result) :
                SafeTransport protectedVars initial result.2 ∧ Safe protectedVars result.2 result.1.type ∧
                  LiveBindersSafe protectedVars result.2 ∧
                  ∀ row ∈ result.2.requirements, row ∉ initial.requirements → PredicateSafe protectedVars result.2 row.predicate := by
              have inferredPrivacy := inferBinaryOperator_private catalog rightProperties.2.1 leftAtRight rightProperties.2.2
                expectedAtRight leftSafeAtRight rightPrivacy.2.1 expectedSafeAtRight rightPrivacy.2.2.1 inferenceSuccess
              have inferredProperties :=
                inferBinaryOperator_inferenceProperties
                  rightProperties.2.1 leftAtRight rightProperties.2.2
                  expectedAtRight inferenceSuccess
              have expectedAtInferred : ∀ expectedType ∈ expected,
                  expectedType.VariablesBelow
                    inferred.state.inference.next := by
                intro expectedType member
                exact (expectedAtRight expectedType member).weaken
                  inferredProperties.1.next_le
              have recorded := recordExpressionWithExpected_private catalog inferredProperties.2.1 inferredProperties.2.2
                expectedAtInferred inferredPrivacy.2.1 (fun type member => inferredPrivacy.1 _ (expectedSafeAtRight _ member))
                inferredPrivacy.2.2.1 recordSuccess
              have tailTransport := inferredPrivacy.1.trans recorded.1
              refine ⟨beforeRight.trans tailTransport, recorded.2.1, recorded.2.2.1, ?_⟩
              intro row member fresh
              exact new_requirements_trans beforeRightRows
                (new_requirements_trans inferredPrivacy.2.2.2 recorded.2.2.2 recorded.1)
                tailTransport row member (by simpa only [allocationPrivacy.2.2] using fresh)
            cases dispatchEq : binaryOperatorDispatch operator.value with
            | traitMethod traitName methodName =>
                simp only [dispatchEq] at success
                cases inferredResult : inferBinaryOperator context
                    operator.value inferredLeft.type inferredRight.type expected
                    integerLiterals rightState with
                | error error =>
                    simp [integerLiterals, inferredResult]
                      at success
                | ok inferred =>
                    simp only [integerLiterals, inferredResult] at success
                    exact finishInferred inferred inferredResult success
            | function name =>
                simp only [dispatchEq] at success
                cases functionsResult : functionsNamed context name with
                | error error =>
                    simp [functionsResult] at success
                | ok candidates =>
                    simp only [functionsResult] at success
                    cases candidates with
                    | nil =>
                        cases inferredResult : inferBinaryOperator context
                            operator.value inferredLeft.type inferredRight.type
                            expected integerLiterals rightState with
                        | error error =>
                            simp [integerLiterals, inferredResult] at success
                        | ok inferred =>
                            simp only [integerLiterals, inferredResult] at success
                            exact finishInferred inferred inferredResult success
                    | cons candidate rest =>
                        cases selectionResult : selectFunctionCandidateFrom
                            context name (candidate :: rest)
                            [inferredLeft, inferredRight] integerLiterals id
                            (some .bool) rightState with
                        | error error =>
                            simp [integerLiterals, selectionResult] at success
                        | ok attempt =>
                            simp only [integerLiterals, selectionResult] at success
                            have selectedProperties :=
                              selectFunctionCandidateFrom_inferenceProperties
                                rightProperties.2.1 argumentsBelow
                                (functionCandidates_scheme_body_variablesBelow (context := context)
                                  validated canonical
                                  (functionsNamed_success_subset_catalog
                                    functionsResult) _)
                                (by
                                  intro expectedType member
                                  simp only [Option.mem_def] at member
                                  injection member with typeEq
                                  subst expectedType
                                  exact Ty.variablesBelow_constructor _ _)
                                selectionResult
                            have selectedPrivacy := selectFunctionCandidateFrom_private catalog
                              (functionsNamed_success_subset_catalog functionsResult) rightProperties.2.1
                              (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) prefixProgress.next_le)
                              argumentsBelow (by
                                intro type member
                                have same := Option.mem_def.mp member
                                injection same with same
                                subst type
                                exact Ty.variablesBelow_constructor _ _)
                              argumentsSafe (by
                                intro type member
                                have same := Option.mem_def.mp member
                                injection same with same
                                subst type
                                exact safe_closed _ _ (Ty.variablesBelow_constructor _ _))
                              rightPrivacy.2.2.1 selectionResult
                            have expectedAtAttempt :
                                ∀ expectedType ∈ expected,
                                  expectedType.VariablesBelow
                                    attempt.state.inference.next := by
                              intro expectedType member
                              exact (expectedAtRight expectedType member).weaken
                                selectedProperties.1.next_le
                            cases fittedResult : withExpected context
                                attempt.state attempt.result expected with
                            | error error =>
                                simp [fittedResult]
                                  at success
                            | ok fitted =>
                                simp only [fittedResult, pure, Pure.pure, Except.pure] at success
                                have expectedSafeAtAttempt : ∀ type ∈ expected, Safe protectedVars attempt.state type :=
                                  fun type member => selectedPrivacy.1 _ (expectedSafeAtRight _ member)
                                have fittedPrivacy := withExpected_private selectedProperties.2.1 selectedProperties.2.2
                                  expectedAtAttempt selectedPrivacy.2.1 expectedSafeAtAttempt selectedPrivacy.2.2.1 fittedResult
                                have fittedRows := withExpected_new_requirements_private catalog selectedProperties.2.1
                                  selectedPrivacy.2.1 expectedSafeAtAttempt fittedResult
                                let callee : Syntax.Expr := {
                                  span := operator.span
                                  value := .identifier {
                                    span := operator.span
                                    value := name
                                  }
                                }
                                change Except.ok
                                  (recordSelectedCallResult expression callee
                                    name [inferredLeft, inferredRight] attempt
                                    fitted.expression fitted.coercions
                                    fitted.state) = Except.ok result at success
                                injection success with resultEq
                                have recorded := recordSelectedCallResult_private expression callee name
                                  [inferredLeft, inferredRight] attempt fitted.expression fitted.coercions fitted.state
                                  fittedPrivacy.2.1 fittedPrivacy.2.2
                                rw [← resultEq]
                                have tailTransport := selectedPrivacy.1.trans (fittedPrivacy.1.trans recorded.1)
                                refine ⟨beforeRight.trans tailTransport, recorded.2.1, recorded.2.2.1, ?_⟩
                                intro row member fresh
                                exact new_requirements_trans beforeRightRows
                                  (new_requirements_trans selectedPrivacy.2.2.2
                                    (new_requirements_trans fittedRows (new_rows_of_eq recorded.2.2.2) recorded.1)
                                    (fittedPrivacy.1.trans recorded.1))
                                  tailTransport row member (by simpa only [allocationPrivacy.2.2] using fresh)

  case case14 =>
    intros context expression expected initial fuel id allocated allocationEq
      condition question thenBranch colon elseBranch expressionEq
      conditionInduction thenInduction elseInduction
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases conditionResult : inferExprFuel fuel context condition
        (some .bool) allocated with
    | error error =>
        simp [conditionResult] at success
    | ok conditionPair =>
        rcases conditionPair with ⟨inferredCondition, conditionState⟩
        simp only [conditionResult] at success
        have conditionProperties := inferExprFuel_inferenceProperties
          allocationProperties.2 validated canonical
          (by
            intro expectedType member
            simp only [Option.mem_def] at member
            injection member with typeEq
            subst expectedType
            exact Ty.variablesBelow_constructor _ _)
          conditionResult
        have conditionPrivacy := conditionInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical (by
            intro type member
            have same := Option.mem_def.mp member
            injection same with same
            subst type
            exact Ty.variablesBelow_constructor _ _) (by
            intro type member
            have same := Option.mem_def.mp member
            injection same with same
            subst type
            exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _))
          (inferredCondition, conditionState) conditionResult
        have toCondition := allocationPrivacy.1.trans conditionPrivacy.1
        have throughCondition :=
          allocationProperties.1.trans conditionProperties.1
        have expectedAtCondition : ∀ expectedType ∈ expected,
            expectedType.VariablesBelow conditionState.inference.next := by
          intro expectedType member
          exact (expectedBelow expectedType member).weaken
            throughCondition.next_le
        cases thenResult : inferExprFuel fuel context thenBranch expected
            conditionState with
        | error error =>
            simp [thenResult] at success
        | ok thenPair =>
            rcases thenPair with ⟨inferredThen, thenState⟩
            simp only [thenResult] at success
            have thenProperties := inferExprFuel_inferenceProperties
              conditionProperties.2.1 validated canonical expectedAtCondition
              thenResult
            have thenPrivacy := thenInduction conditionState conditionProperties.2.1
              ((inferExprFuel_direct_progress conditionResult).wellFormed wfAllocated)
              (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughCondition.next_le)
              conditionPrivacy.2.2.1 catalog validated canonical expectedAtCondition
              (fun type member => toCondition _ (expectedSafe type member))
              (inferredThen, thenState) thenResult
            have toThen := toCondition.trans thenPrivacy.1
            have throughThen := throughCondition.trans thenProperties.1
            have expectedAtThen : ∀ expectedType ∈ expected,
                expectedType.VariablesBelow thenState.inference.next := by
              intro expectedType member
              exact (expectedBelow expectedType member).weaken
                throughThen.next_le
            cases elseResult : inferExprFuel fuel context elseBranch expected
                thenState with
            | error error =>
                simp [elseResult] at success
            | ok elsePair =>
                rcases elsePair with ⟨inferredElse, elseState⟩
                simp only [elseResult] at success
                have elseProperties := inferExprFuel_inferenceProperties
                  thenProperties.2.1 validated canonical expectedAtThen
                  elseResult
                have elsePrivacy := elseInduction thenState thenProperties.2.1
                  ((inferExprFuel_direct_progress thenResult).wellFormed
                    ((inferExprFuel_direct_progress conditionResult).wellFormed wfAllocated))
                  (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughThen.next_le)
                  thenPrivacy.2.2.1 catalog validated canonical expectedAtThen
                  (fun type member => toThen _ (expectedSafe type member))
                  (inferredElse, elseState) elseResult
                have toElse := toThen.trans elsePrivacy.1
                have thenSafe := elsePrivacy.1 _ thenPrivacy.2.1
                have thenAtElse : inferredThen.type.VariablesBelow
                    elseState.inference.next :=
                  thenProperties.2.2.weaken elseProperties.1.next_le
                cases unifyResult : Detail.unify elseState inferredThen.type
                    inferredElse.type with
                | error error =>
                    simp [unifyResult] at success
                | ok unifiedState =>
                    simp only [unifyResult] at success
                    have unifyProgress := unify_inferenceProgress
                      elseProperties.2.1.solved thenAtElse
                      elseProperties.2.2 unifyResult
                    have unifiedReady := unify_preserves_inferenceReady
                      elseProperties.2.1 thenAtElse elseProperties.2.2
                      unifyResult
                    have throughUnify := throughThen.trans
                      (elseProperties.1.trans unifyProgress)
                    have resolvedThenBelow :
                        (unifiedState.resolve inferredThen.type).VariablesBelow
                          unifiedState.inference.next :=
                      unifyProgress.resolve_variablesBelow thenAtElse
                    have expectedAtUnified : ∀ expectedType ∈ expected,
                        expectedType.VariablesBelow
                          unifiedState.inference.next := by
                      intro expectedType member
                      exact (expectedBelow expectedType member).weaken
                        throughUnify.next_le
                    have unifyPrivacy := ProtectedVariables.unify thenSafe elsePrivacy.2.1 unifyResult
                    have toUnified := toElse.trans unifyPrivacy
                    have unifiedLive := elsePrivacy.2.2.1.unify thenSafe elsePrivacy.2.1 unifyResult
                    have recorded := recordExpressionWithExpected_private catalog unifiedReady
                      resolvedThenBelow expectedAtUnified
                      (safe_resolved unifiedReady (unifyPrivacy _ thenSafe))
                      (fun type member => toUnified _ (expectedSafe type member)) unifiedLive success
                    refine ⟨toUnified.trans recorded.1, recorded.2.1, recorded.2.2.1, ?_⟩
                    have bodyRows := new_requirements_trans conditionPrivacy.2.2.2
                      (new_requirements_trans thenPrivacy.2.2.2 elsePrivacy.2.2.2 elsePrivacy.1)
                      (thenPrivacy.1.trans elsePrivacy.1)
                    have unifiedRows := new_requirements_trans bodyRows
                      (new_rows_of_eq (unify_requirements unifyResult)) unifyPrivacy
                    intro row member freshRow
                    exact new_requirements_trans unifiedRows recorded.2.2.2 recorded.1 row member
                      (by simpa only [allocationPrivacy.2.2] using freshRow)
  case case15 =>
    intro context expression expected initial fuel id allocated allocation keyword parameters returnType body form bodyIH
    exact inferExprFuel_lambda_private form bodyIH

  case case21 =>
    simp_all [InferExprFuelPrivacy, inferExprFuel]
  case case22 =>
    simp_all [InferExprFuelPrivacy, inferExprFuel]
  case case24 =>
    simp_all [InferConstructorApplicationFuelPrivacy,
      inferConstructorApplicationFuel, bind, Except.bind]
  case case27 =>
    simp_all [InferConstructorArgumentsFuelPrivacy,
      inferConstructorArgumentsFuel]
  case case28 =>
    simp [InferStatementsFuelPrivacy, inferStatementsFuel]
  case case31 =>
    simp [InferStatementFuelPrivacy, inferStatementFuel]
  case case32 =>
    simp_all [InferStatementFuelPrivacy, inferStatementFuel,
      bind, Except.bind]
  case case47 =>
    simp_all [InferStatementFuelPrivacy, inferStatementFuel]
  case case48 =>
    simp_all [InferStatementFuelPrivacy, inferStatementFuel]
  case case50 =>
    simp_all [InferStatementFuelPrivacy, inferStatementFuel]
  case case52 =>
    simp_all [InferStatementFuelPrivacy, inferStatementFuel]
  case case55 =>
    simp [InferForItemFuelPrivacy, inferForItemFuel]
  case case56 =>
    simp_all [InferForItemFuelPrivacy, inferForItemFuel, bind,
      Except.bind]
  case case63 =>
    simp [InferPlaceFuelPrivacy, inferPlaceFuel]
  case case65 =>
    simp_all [InferPlaceFuelPrivacy, inferPlaceFuel]
  case case66 =>
    simp_all [InferPlaceFuelPrivacy, inferPlaceFuel]
  case case69 =>
    simp_all [InferPlaceFuelPrivacy, inferPlaceFuel]
  case case71 =>
    simp [InferExprsFuelPrivacy, inferExprsFuel]
  case case74 =>
    simp [InferMatchCasesFuelPrivacy, inferMatchCasesFuel]
  case case25 =>
    intros fuel context initial
    unfold InferConstructorArgumentsFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical below safe result success
    unfold inferConstructorArgumentsFuel at success
    injection success with resultEq
    subst result
    exact ⟨.refl _ _, by simp, live, new_rows_of_eq rfl⟩
  case case29 =>
    intros context expectedReturn initial fuel
    unfold InferStatementsFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical below safe result success
    unfold inferStatementsFuel at success
    injection success with resultEq
    subst result
    exact ⟨.refl _ _, safe_closed _ _ (Ty.variablesBelow_constructor 0 _), live, new_rows_of_eq rfl⟩
  case case53 =>
    intros fuel context initial
    unfold InferForItemsFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferForItemsFuel at success
    injection success with resultEq
    subst result
    exact ⟨.refl _ _, live, new_rows_of_eq rfl⟩
  case case72 =>
    intros context initial fuel
    unfold InferExprsFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferExprsFuel at success
    injection success with resultEq
    subst result
    exact ⟨.refl _ _, by simp, live, new_rows_of_eq rfl⟩
  case case75 =>
    intros context scrutineeType expectedReturn outerScope initial fuel
    unfold InferMatchCasesFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical scrutineeBelow scrutineeSafe returnBelow returnSafe scopeEq result success
    unfold inferMatchCasesFuel at success
    injection success with resultEq
    subst result
    exact ⟨.refl _ _, live, new_rows_of_eq rfl⟩


  case case54 =>
    intros fuel context item items initial itemIH tailIH
    unfold InferForItemsFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferForItemsFuel at success
    cases itemRun : inferForItemFuel fuel context item initial with
    | error error => simp [itemRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨inferred, itemState⟩
      simp only [itemRun, bind, Except.bind] at success
      cases tailRun : inferForItemsFuel fuel context items itemState with
      | error error => simp [tailRun] at success
      | ok tail =>
        simp only [tailRun] at success
        cases success
        have itemProperties := inferForItemFuel_inferenceProperties ready validated canonical itemRun
        have itemPrivacy := itemIH ready wellFormed bound live catalog validated canonical _ itemRun
        have tailPrivacy := tailIH itemState itemProperties.2
          ((inferForItemFuel_direct_progress itemRun).wellFormed wellFormed)
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) itemProperties.1.next_le)
          itemPrivacy.2.1 catalog validated canonical tail tailRun
        exact ⟨itemPrivacy.1.trans tailPrivacy.1, tailPrivacy.2.1,
          new_requirements_trans itemPrivacy.2.2 tailPrivacy.2.2 tailPrivacy.1⟩
  case case73 =>
    intros context initial fuel expression rest expressionIH tailIH
    unfold InferExprsFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferExprsFuel at success
    cases expressionRun : inferExprFuel fuel context expression none initial with
    | error error => simp [expressionRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨inferred, expressionState⟩
      simp only [expressionRun, bind, Except.bind] at success
      cases tailRun : inferExprsFuel fuel context rest expressionState with
      | error error => simp [tailRun] at success
      | ok pair =>
        rcases pair with ⟨tail, finalState⟩
        simp only [tailRun] at success
        cases success
        have expressionProperties := inferExprFuel_inferenceProperties ready validated canonical (by simp) expressionRun
        have expressionPrivacy := expressionIH ready wellFormed bound live catalog validated canonical
          (by simp) (by simp) _ expressionRun
        have tailPrivacy := tailIH expressionState expressionProperties.2.1
          ((inferExprFuel_direct_progress expressionRun).wellFormed wellFormed)
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) expressionProperties.1.next_le)
          expressionPrivacy.2.2.1 catalog validated canonical _ tailRun
        refine ⟨expressionPrivacy.1.trans tailPrivacy.1, ?_, tailPrivacy.2.2.1,
          new_requirements_trans expressionPrivacy.2.2.2 tailPrivacy.2.2.2 tailPrivacy.1⟩
        intro element member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact tailPrivacy.1 _ expressionPrivacy.2.1
        · exact tailPrivacy.2.1 element tailMember

  case case60 =>
    intros context item initial fuel expression itemEq expressionInduction
    unfold InferForItemFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases expressionResult : inferExprFuel fuel context expression none initial with
    | error error =>
        simp [expressionResult] at success
    | ok expressionPair =>
        rcases expressionPair with ⟨inferred, expressionState⟩
        simp only [expressionResult, pure, Pure.pure, Except.pure] at success
        injection success with resultEq
        rw [← resultEq]
        have expressionProperties := expressionInduction ready wellFormed bound live catalog validated
          canonical (by simp) (by simp) (inferred, expressionState) expressionResult
        exact ⟨expressionProperties.1, expressionProperties.2.2.1, expressionProperties.2.2.2⟩
  case case61 =>
    intros context item initial fuel target operator value itemEq
      assignmentInduction
    unfold InferForItemFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases assignmentResult : inferAssignedValueFuel fuel context target
        operator.value value initial with
    | error error =>
        simp [assignmentResult] at success
    | ok assignmentTriple =>
        rcases assignmentTriple with
          ⟨assignment, inferredValue, assignmentState⟩
        simp only [assignmentResult, pure, Pure.pure, Except.pure] at success
        injection success with resultEq
        rw [← resultEq]
        have assignmentProperties := assignmentInduction ready wellFormed bound live catalog validated
          canonical (assignment, inferredValue, assignmentState)
          assignmentResult
        exact ⟨assignmentProperties.1, assignmentProperties.2.2.2.1, assignmentProperties.2.2.2.2⟩
  case case62 =>
    intros context item initial fuel target operator itemEq placeInduction
    unfold InferForItemFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases placeResult : inferPlaceFuel fuel context target initial with
    | error error =>
        simp [placeResult] at success
    | ok placePair =>
        rcases placePair with ⟨place, placeState⟩
        simp only [placeResult] at success
        have placeProperties := placeInduction ready wellFormed bound live catalog validated canonical
          (place, placeState) placeResult
        cases unifyResult : Detail.unify placeState place.type .word with
        | error error =>
            simp [unifyResult] at success
        | ok unifiedState =>
            simp only [unifyResult, pure, Pure.pure, Except.pure] at success
            injection success with resultEq
            rw [← resultEq]
            have wordSafe : Safe protectedVars placeState .word := safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
            have unifiedPrivacy := ProtectedVariables.unify placeProperties.2.1 wordSafe unifyResult
            exact ⟨placeProperties.1.trans unifiedPrivacy,
              placeProperties.2.2.1.unify placeProperties.2.1 wordSafe unifyResult,
              new_requirements_trans placeProperties.2.2.2
                (new_rows_of_eq (unify_requirements unifyResult)) unifiedPrivacy⟩

  case case67 =>
    intros context target initial fuel inner targetEq innerIH
    unfold InferPlaceFuelPrivacy at *
    intro ready wellFormed bound live catalog validated canonical result success
    apply innerIH ready wellFormed bound live catalog validated canonical result
    simpa only [inferPlaceFuel, targetEq] using success
  case case26 =>
    intros fuel context source sources expected expectedTypes initial sourceIH tailIH
    unfold InferConstructorArgumentsFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    unfold inferConstructorArgumentsFuel at success
    cases sourceRun : inferExprFuel fuel context source (some (initial.resolve expected)) initial with
    | error error => simp [sourceRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨inferred, sourceState⟩
      simp only [sourceRun, bind, Except.bind] at success
      cases tailRun : inferConstructorArgumentsFuel fuel context sources expectedTypes sourceState with
      | error error => simp [tailRun] at success
      | ok pair =>
        rcases pair with ⟨tail, finalState⟩
        simp only [tailRun] at success
        cases success
        have expectedTypeBelow := expectedBelow expected (by simp)
        have fitBelow : ∀ type ∈ some (initial.resolve expected), type.VariablesBelow initial.inference.next := by
          intro type member
          simp only [Option.mem_def] at member
          injection member with same
          subst type
          exact ready.solved.variablesBelow_apply expectedTypeBelow
        have fitSafe : ∀ type ∈ some (initial.resolve expected), Safe protectedVars initial type := by
          intro type member
          simp only [Option.mem_def] at member
          injection member with same
          subst type
          exact safe_resolved ready (expectedSafe expected (by simp))
        have sourceProperties := inferExprFuel_inferenceProperties ready validated canonical fitBelow sourceRun
        have sourcePrivacy := sourceIH ready wellFormed bound live catalog validated canonical
          fitBelow fitSafe _ sourceRun
        have tailPrivacy := tailIH sourceState sourceProperties.2.1
          ((inferExprFuel_direct_progress sourceRun).wellFormed wellFormed)
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) sourceProperties.1.next_le)
          sourcePrivacy.2.2.1 catalog validated canonical
          (fun type member => (expectedBelow type (by simp [member])).weaken sourceProperties.1.next_le)
          (fun type member => sourcePrivacy.1 _ (expectedSafe type (by simp [member]))) _ tailRun
        refine ⟨sourcePrivacy.1.trans tailPrivacy.1, ?_, tailPrivacy.2.2.1,
          new_requirements_trans sourcePrivacy.2.2.2 tailPrivacy.2.2.2 tailPrivacy.1⟩
        intro element member
        rcases List.mem_cons.mp member with rfl | member
        · exact tailPrivacy.1 _ sourcePrivacy.2.1
        · exact tailPrivacy.2.1 element member

  case case76 =>
    intros context scrutineeType expectedReturn outerScope initial fuel arm rest bodyIH tailIH
    exact inferMatchCasesFuel_cons_private bodyIH tailIH
  case case23 =>
    intros fuel context source id instantiation arguments expected initial
      arityEq argumentsInduction
    unfold InferConstructorApplicationFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical payloadTypesBelow payloadSafe resultTypeBelow resultSafe
      expectedBelow expectedSafe result success
    unfold inferConstructorApplicationFuel at success
    simp only [arityEq, bind, Except.bind] at success
    let fittedComputation : Except Error State :=
      match expected with
      | none => pure initial
      | some expectedType => Detail.unify initial instantiation.resultType expectedType
    have fittedProperties : ∀ fittedState,
        fittedComputation = .ok fittedState →
        initial.InferenceProgress fittedState ∧
          fittedState.InferenceReady := by
      intro fittedState fittedSuccess
      unfold fittedComputation at fittedSuccess
      cases expected with
      | none =>
          simp only [pure, Pure.pure, Except.pure] at fittedSuccess
          injection fittedSuccess with stateEq
          subst fittedState
          exact ⟨State.InferenceProgress.refl ready.solved, ready⟩
      | some expectedType =>
          exact ⟨unify_inferenceProgress ready.solved resultTypeBelow
              (expectedBelow expectedType (by simp)) fittedSuccess,
            unify_preserves_inferenceReady ready resultTypeBelow
              (expectedBelow expectedType (by simp)) fittedSuccess⟩
    cases expected with
    | none =>
        simp only [pure, Pure.pure, Except.pure] at success
        cases argumentsResult : inferConstructorArgumentsFuel fuel context
            arguments instantiation.payloadTypes initial with
        | error error =>
            simp [argumentsResult] at success
        | ok argumentsPair =>
            rcases argumentsPair with ⟨inferredArguments, argumentsState⟩
            simp only [argumentsResult] at success
            have argumentsProperties := inferConstructorArgumentsFuel_inferenceProperties ready
              validated canonical payloadTypesBelow argumentsResult
            have argumentsPrivacy := argumentsInduction initial ready wellFormed bound live catalog validated canonical
              payloadTypesBelow payloadSafe _ argumentsResult
            have resultAtArguments :=
              argumentsProperties.1.resolve_variablesBelow resultTypeBelow
            have recorded := recordExpressionWithExpected_private catalog argumentsProperties.2.1
              resultAtArguments (by simp)
              (safe_resolved argumentsProperties.2.1 (argumentsPrivacy.1 _ resultSafe))
              (by simp) argumentsPrivacy.2.2.1 success
            exact ⟨argumentsPrivacy.1.trans recorded.1, recorded.2.1, recorded.2.2.1,
              new_requirements_trans argumentsPrivacy.2.2.2 recorded.2.2.2 recorded.1⟩
    | some expectedType =>
        cases fittedResult : Detail.unify initial instantiation.resultType
            expectedType with
        | error error =>
            simp [fittedResult] at success
        | ok fittedState =>
            simp only [fittedResult] at success
            have fitProperties := fittedProperties fittedState (by
              simpa only [fittedComputation] using fittedResult)
            have fitTransport := ProtectedVariables.unify resultSafe (expectedSafe expectedType (by simp)) fittedResult
            have fitLive := live.unify resultSafe (expectedSafe expectedType (by simp)) fittedResult
            have payloadAtFitted : ∀ payload ∈ instantiation.payloadTypes,
                payload.VariablesBelow fittedState.inference.next := by
              intro payload member
              exact (payloadTypesBelow payload member).weaken
                fitProperties.1.next_le
            cases argumentsResult : inferConstructorArgumentsFuel fuel context
                arguments instantiation.payloadTypes fittedState with
            | error error =>
                simp [argumentsResult] at success
            | ok argumentsPair =>
                rcases argumentsPair with
                  ⟨inferredArguments, argumentsState⟩
                simp only [argumentsResult]
                  at success
                have argumentsProperties := inferConstructorArgumentsFuel_inferenceProperties
                  fitProperties.2 validated canonical payloadAtFitted argumentsResult
                have argumentsPrivacy := argumentsInduction fittedState fitProperties.2
                  (unify_preserves_requirementsWellFormed fittedResult wellFormed)
                  (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) fitProperties.1.next_le)
                  fitLive catalog validated canonical payloadAtFitted
                  (fun type member => fitTransport _ (payloadSafe type member)) _ argumentsResult
                have throughArguments :=
                  fitProperties.1.trans argumentsProperties.1
                have resultAtArguments :=
                  throughArguments.resolve_variablesBelow resultTypeBelow
                have expectedAtArguments : ∀ candidate : Ty,
                    candidate ∈ some expectedType →
                    candidate.VariablesBelow
                      argumentsState.inference.next := by
                  intro candidate member
                  simp only [Option.mem_def] at member
                  injection member with typeEq
                  subst candidate
                  exact (expectedBelow expectedType (by simp)).weaken
                    throughArguments.next_le
                have toArguments := fitTransport.trans argumentsPrivacy.1
                have recorded := recordExpressionWithExpected_private catalog argumentsProperties.2.1
                  resultAtArguments expectedAtArguments
                  (safe_resolved argumentsProperties.2.1 (toArguments _ resultSafe))
                  (fun type member => toArguments _ (expectedSafe type member)) argumentsPrivacy.2.2.1 success
                refine ⟨toArguments.trans recorded.1, recorded.2.1, recorded.2.2.1, ?_⟩
                intro row member freshRow
                exact new_requirements_trans argumentsPrivacy.2.2.2 recorded.2.2.2 recorded.1 row member
                  (by simpa only [unify_requirements fittedResult] using freshRow)
  case case58 =>
    intros context item initial fuel name initializer itemEq
      initializerInduction
    unfold InferForItemFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases initializerResult : inferExprFuel fuel context initializer none
        initial with
    | error error =>
        simp [initializerResult] at success
    | ok initializerPair =>
        rcases initializerPair with ⟨inferred, initializerState⟩
        simp only [initializerResult, pure, Pure.pure, Except.pure] at success
        have initializerProperties := inferExprFuel_inferenceProperties ready validated canonical (by simp) initializerResult
        have initializerPrivacy := initializerInduction ready wellFormed bound live catalog validated canonical
          (by simp) (by simp) _ initializerResult
        let binding :=
          let locals := initializerState.binderEnvironment.apply
            initializerState.inference.substitution
          let valueType := initializerState.resolve inferred.type
          let generalized := generalizeValue initializerState locals
            initial.nextRequirement valueType
          (initializerState.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        have bindingPrivacy := generalize_binding_private name.value (some name.span) wellFormed
          ((inferExprFuel_direct_progress initializerResult).wellFormed wellFormed)
          initializerProperties.2.1 initializerPrivacy.2.1 initializerPrivacy.2.2.1 initializerPrivacy.2.2.2
        injection success with resultEq
        rw [← resultEq]
        refine ⟨initializerPrivacy.1.trans bindingPrivacy.1, bindingPrivacy.2.1, ?_⟩
        exact new_requirements_trans initializerPrivacy.2.2.2
          (new_rows_of_eq bindingPrivacy.2.2) bindingPrivacy.1
  case case34 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq name initializer statementEq initializerInduction
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases initializerResult : inferExprFuel fuel context initializer none
        allocated with
    | error error =>
        simp [initializerResult] at success
    | ok initializerPair =>
        rcases initializerPair with ⟨inferred, initializerState⟩
        simp only [initializerResult, pure, Pure.pure, Except.pure] at success
        have initializerProperties := inferExprFuel_inferenceProperties
          allocationProperties.2 validated canonical (by simp) initializerResult
        have initializerPrivacy := initializerInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical (by simp) (by simp) _ initializerResult
        let binding :=
          let locals := initializerState.binderEnvironment.apply
            initializerState.inference.substitution
          let valueType := initializerState.resolve inferred.type
          let generalized := generalizeValue initializerState locals
            allocated.nextRequirement valueType
          (initializerState.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        have bindingPrivacy := generalize_binding_private (before := allocated) name.value (some name.span) wfAllocated
          ((inferExprFuel_direct_progress initializerResult).wellFormed wfAllocated)
          initializerProperties.2.1 initializerPrivacy.2.1 initializerPrivacy.2.2.1 initializerPrivacy.2.2.2
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationPrivacy.1.trans (initializerPrivacy.1.trans
          (bindingPrivacy.1.trans (.of_substitution_eq rfl))),
          safe_closed _ _ (Ty.variablesBelow_constructor 0 _), ?_, ?_⟩
        · exact bindingPrivacy.2.1.transport rfl (.of_substitution_eq rfl)
        · intro row member freshRow type typeMember
          apply SafeTransport.of_substitution_eq (before := initializerState) rfl
          exact initializerPrivacy.2.2.2 row member
            (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember
  case case33 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq name sourceType statementEq
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult] at success
    | ok resolvedType =>
        simp only [sourceTypeResult, pure, Pure.pure, Except.pure] at success
        let binding :=
          let locals := allocated.binderEnvironment.apply
            allocated.inference.substitution
          let valueType := allocated.resolve resolvedType
          let generalized := generalizeValue allocated locals
            allocated.nextRequirement valueType
          (allocated.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        have bindingPrivacy := generalize_binding_private (before := allocated) name.value (some name.span) wfAllocated wfAllocated
          allocationProperties.2 (safe_closed _ _ (resolveSourceType_success_variablesBelow sourceTypeResult 0)) allocationPrivacy.2.1 (new_rows_of_eq rfl)
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationPrivacy.1.trans (bindingPrivacy.1.trans (.of_substitution_eq rfl)),
          safe_closed _ _ (Ty.variablesBelow_constructor 0 _), ?_, ?_⟩
        · exact bindingPrivacy.2.1.transport rfl (.of_substitution_eq rfl)
        · exact new_rows_of_eq allocationPrivacy.2.2

  case case57 =>
    intros context item initial fuel name sourceType itemEq
    unfold InferForItemFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult] at success
    | ok resolvedType =>
        simp only [sourceTypeResult, pure, Pure.pure, Except.pure] at success
        let binding :=
          let locals := initial.binderEnvironment.apply
            initial.inference.substitution
          let valueType := initial.resolve resolvedType
          let generalized := generalizeValue initial locals
            initial.nextRequirement valueType
          (initial.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        have bindingPrivacy := generalize_binding_private (before := initial) name.value (some name.span) wellFormed wellFormed
          ready (safe_closed _ _ (resolveSourceType_success_variablesBelow sourceTypeResult 0)) live (new_rows_of_eq rfl)
        injection success with resultEq
        rw [← resultEq]
        exact ⟨bindingPrivacy.1, bindingPrivacy.2.1, new_rows_of_eq bindingPrivacy.2.2⟩

  case case35 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq name sourceType initializer statementEq
      initializerInduction
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult] at success
    | ok resolvedType =>
        simp only [sourceTypeResult] at success
        have resolvedTypeBelow :
            resolvedType.VariablesBelow allocated.inference.next :=
          resolveSourceType_success_variablesBelow sourceTypeResult _
        cases initializerResult : inferExprFuel fuel context initializer
            (some resolvedType) allocated with
        | error error =>
            simp [initializerResult] at success
        | ok initializerPair =>
            rcases initializerPair with ⟨inferred, initializerState⟩
            simp only [initializerResult, pure, Pure.pure, Except.pure] at success
            have initializerProperties := inferExprFuel_inferenceProperties
              allocationProperties.2 validated canonical
              (by
                intro expectedType member
                simp only [Option.mem_def] at member
                injection member with typeEq
                subst expectedType
                exact resolvedTypeBelow)
              initializerResult
            have initializerPrivacy := initializerInduction resolvedType allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1 catalog validated canonical
              (by
                intro type member
                simp only [Option.mem_def] at member
                injection member with same
                subst type
                exact resolvedTypeBelow)
              (by
                intro type member
                simp only [Option.mem_def] at member
                injection member with same
                subst type
                exact safe_closed _ _ (resolveSourceType_success_variablesBelow sourceTypeResult 0)) _ initializerResult
            let binding :=
              let locals := initializerState.binderEnvironment.apply
                initializerState.inference.substitution
              let valueType := initializerState.resolve inferred.type
              let generalized := generalizeValue initializerState locals
                allocated.nextRequirement valueType
              (initializerState.withLocals locals).allocateBinder name.value
                generalized.scheme (some name.span) false
                generalized.requirements
            have bindingPrivacy := generalize_binding_private (before := allocated) name.value (some name.span) wfAllocated
              ((inferExprFuel_direct_progress initializerResult).wellFormed wfAllocated)
              initializerProperties.2.1 initializerPrivacy.2.1 initializerPrivacy.2.2.1 initializerPrivacy.2.2.2
            injection success with resultEq
            rw [← resultEq]
            refine ⟨allocationPrivacy.1.trans (initializerPrivacy.1.trans (bindingPrivacy.1.trans (.of_substitution_eq rfl))),
              safe_closed _ _ (Ty.variablesBelow_constructor 0 _), ?_, ?_⟩
            · exact bindingPrivacy.2.1.transport rfl (.of_substitution_eq rfl)
            · intro row member freshRow type typeMember
              apply SafeTransport.of_substitution_eq (before := initializerState) rfl
              exact initializerPrivacy.2.2.2 row member
                (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember

  case case59 =>
    intros context item initial fuel name sourceType initializer itemEq
      initializerInduction
    unfold InferForItemFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult] at success
    | ok resolvedType =>
        simp only [sourceTypeResult] at success
        have resolvedTypeBelow :
            resolvedType.VariablesBelow initial.inference.next :=
          resolveSourceType_success_variablesBelow sourceTypeResult _
        cases initializerResult : inferExprFuel fuel context initializer
            (some resolvedType) initial with
        | error error =>
            simp [initializerResult] at success
        | ok initializerPair =>
            rcases initializerPair with ⟨inferred, initializerState⟩
            simp only [initializerResult, pure, Pure.pure, Except.pure] at success
            have initializerProperties := inferExprFuel_inferenceProperties
              ready validated canonical
              (by
                intro expectedType member
                simp only [Option.mem_def] at member
                injection member with typeEq
                subst expectedType
                exact resolvedTypeBelow)
              initializerResult
            have initializerPrivacy := initializerInduction resolvedType ready wellFormed bound live catalog validated canonical
              (by
                intro type member
                simp only [Option.mem_def] at member
                injection member with same
                subst type
                exact resolvedTypeBelow)
              (by
                intro type member
                simp only [Option.mem_def] at member
                injection member with same
                subst type
                exact safe_closed _ _ (resolveSourceType_success_variablesBelow sourceTypeResult 0)) _ initializerResult
            let binding :=
              let locals := initializerState.binderEnvironment.apply
                initializerState.inference.substitution
              let valueType := initializerState.resolve inferred.type
              let generalized := generalizeValue initializerState locals
                initial.nextRequirement valueType
              (initializerState.withLocals locals).allocateBinder name.value
                generalized.scheme (some name.span) false
                generalized.requirements
            have bindingPrivacy := generalize_binding_private (before := initial) name.value (some name.span) wellFormed
              ((inferExprFuel_direct_progress initializerResult).wellFormed wellFormed)
              initializerProperties.2.1 initializerPrivacy.2.1 initializerPrivacy.2.2.1 initializerPrivacy.2.2.2
            injection success with resultEq
            rw [← resultEq]
            exact ⟨initializerPrivacy.1.trans bindingPrivacy.1, bindingPrivacy.2.1,
              new_requirements_trans initializerPrivacy.2.2.2 (new_rows_of_eq bindingPrivacy.2.2) bindingPrivacy.1⟩
  case case38 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq expression trailingSemicolon statementEq
      expressionInduction
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases expressionResult : inferExprFuel fuel context expression none
        allocated with
    | error error =>
        simp [expressionResult] at success
    | ok expressionPair =>
        rcases expressionPair with ⟨inferred, expressionState⟩
        simp only [expressionResult, pure, Pure.pure, Except.pure] at success
        have expressionPrivacy := expressionInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical (by simp) (by simp) _ expressionResult
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationPrivacy.1.trans (expressionPrivacy.1.trans (.of_substitution_eq rfl)),
          ?_, expressionPrivacy.2.2.1.transport rfl (.of_substitution_eq rfl), ?_⟩
        · split
          · exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
          · exact SafeTransport.of_substitution_eq rfl _ expressionPrivacy.2.1
        · intro row member freshRow type typeMember
          apply SafeTransport.of_substitution_eq (before := expressionState) rfl
          exact expressionPrivacy.2.2.2 row member (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember

  case case40 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq body statementEq bodyInduction
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases bodyResultEq : inferStatementsFuel fuel context body expectedReturn
        allocated with
    | error error =>
        simp [bodyResultEq] at success
    | ok bodyResult =>
        simp only [bodyResultEq, pure, Pure.pure, Except.pure] at success
        have bodyPrivacy := bodyInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical
          (returnBelow.weaken allocationProperties.1.next_le) (allocationPrivacy.1 _ returnSafe) _ bodyResultEq
        have restoredLive := allocationPrivacy.2.1.restore bodyPrivacy.1
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationPrivacy.1.trans (bodyPrivacy.1.trans (.of_substitution_eq rfl)),
          SafeTransport.of_substitution_eq rfl _ bodyPrivacy.2.1,
          restoredLive.transport rfl (.of_substitution_eq rfl), ?_⟩
        intro row member freshRow type typeMember
        apply SafeTransport.of_substitution_eq (before := bodyResult.state) rfl
        exact bodyPrivacy.2.2.2 row member (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember

  case case41 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq target operator value statementEq assignmentInduction
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases assignmentResult : inferAssignedValueFuel fuel context target
        operator.value value allocated with
    | error error =>
        simp [assignmentResult] at success
    | ok assignmentTriple =>
        rcases assignmentTriple with
          ⟨assignment, inferredValue, assignmentState⟩
        simp only [assignmentResult, pure, Pure.pure, Except.pure] at success
        have assignmentPrivacy := assignmentInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical _ assignmentResult
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationPrivacy.1.trans (assignmentPrivacy.1.trans (.of_substitution_eq rfl)),
          safe_closed _ _ (Ty.variablesBelow_constructor 0 _),
          assignmentPrivacy.2.2.2.1.transport rfl (.of_substitution_eq rfl), ?_⟩
        intro row member freshRow type typeMember
        apply SafeTransport.of_substitution_eq (before := assignmentState) rfl
        exact assignmentPrivacy.2.2.2.2 row member (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember

  case case42 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq target operator statementEq placeInduction
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases placeResult : inferPlaceFuel fuel context target allocated with
    | error error =>
        simp [placeResult] at success
    | ok placePair =>
        rcases placePair with ⟨inferredTarget, placeState⟩
        simp only [placeResult] at success
        have placePrivacy := placeInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical (inferredTarget, placeState) placeResult
        cases unifyResult : Detail.unify placeState inferredTarget.type .word with
        | error error =>
            simp [unifyResult] at success
        | ok unifiedState =>
            simp only [unifyResult, pure, Pure.pure, Except.pure] at success
            have wordSafe : Safe protectedVars placeState .word := safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
            have unifiedPrivacy := ProtectedVariables.unify placePrivacy.2.1 wordSafe unifyResult
            have unifiedLive := placePrivacy.2.2.1.unify placePrivacy.2.1 wordSafe unifyResult
            injection success with resultEq
            rw [← resultEq]
            refine ⟨allocationPrivacy.1.trans (placePrivacy.1.trans (unifiedPrivacy.trans (.of_substitution_eq rfl))),
              safe_closed _ _ (Ty.variablesBelow_constructor 0 _),
              unifiedLive.transport rfl (.of_substitution_eq rfl), ?_⟩
            have newRows := new_requirements_trans placePrivacy.2.2.2
              (new_rows_of_eq (unify_requirements unifyResult)) unifiedPrivacy
            intro row member freshRow type typeMember
            apply SafeTransport.of_substitution_eq (before := unifiedState) rfl
            exact newRows row member (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember

  case case49 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq statementEq loopNonzero
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    let finalState := allocated.recordNode (.statement {
      id
      span := statement.span
      type := .unit
      form := .breakStmt
    })
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, loopNonzero, if_false] at success
    injection success with resultEq
    subst result
    exact ⟨allocationPrivacy.1.trans (.of_substitution_eq rfl),
      safe_closed _ _ (Ty.variablesBelow_constructor 0 _),
      allocationPrivacy.2.1.transport rfl (.of_substitution_eq rfl), new_rows_of_eq allocationPrivacy.2.2⟩

  case case51 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq statementEq loopNonzero
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    let finalState := allocated.recordNode (.statement {
      id
      span := statement.span
      type := .unit
      form := .continueStmt
    })
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, loopNonzero, if_false] at success
    injection success with resultEq
    subst result
    exact ⟨allocationPrivacy.1.trans (.of_substitution_eq rfl),
      safe_closed _ _ (Ty.variablesBelow_constructor 0 _),
      allocationPrivacy.2.1.transport rfl (.of_substitution_eq rfl), new_rows_of_eq allocationPrivacy.2.2⟩
  case case18 =>
    intros context expression expected initial fuel id allocated allocationEq
      marker sourceType expressionEq
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProperties.1.next_le
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases sourceTypeResult : resolveSourceType context sourceType with
    | error error =>
        simp [sourceTypeResult] at success
    | ok inner =>
        simp only [sourceTypeResult] at success
        have innerBelow :=
          resolveSourceType_success_variablesBelow sourceTypeResult
            allocated.inference.next
        have proxyBelow : (Ty.proxy inner).VariablesBelow
            allocated.inference.next :=
          (Ty.variablesBelow_proxy_iff _ _).2 innerBelow
        have recorded := recordExpressionWithExpected_private catalog allocationProperties.2 proxyBelow expectedAtAllocated
          ((safe_proxy_iff _ _ _).mpr (safe_closed _ _ (resolveSourceType_success_variablesBelow sourceTypeResult 0)))
          (fun type member => allocationPrivacy.1 _ (expectedSafe type member)) allocationPrivacy.2.1 success
        refine ⟨allocationPrivacy.1.trans recorded.1, recorded.2.1, recorded.2.2.1, ?_⟩
        intro row member freshRow
        exact recorded.2.2.2 row member (by simpa only [allocationPrivacy.2.2] using freshRow)

  case case64 =>
    intros context target initial fuel name targetEq binder lookupEq monomorphic
    unfold InferPlaceFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferPlaceFuel at success
    simp only [targetEq, lookupEq, monomorphic, if_true] at success
    injection success with resultEq
    subst result
    have empty : binder.scheme.quantified = [] := List.isEmpty_iff.mp monomorphic
    have binderSafe := live binder (State.lookupBinder?_eq_some_facts lookupEq).1
    have bodySafe := safe_instantiated_type ready bound
      ({quantified := [], body := binder.scheme.body} : Scheme) (by simp) binder.scheme.body
      (by
        intro metavariable occurs outside
        apply binderSafe.body metavariable
        simpa only [Scheme.freeVariables, empty, List.mem_filter, List.not_mem_nil, decide_false, Bool.not_false, and_true] using occurs)
    change Safe protectedVars initial (TypeSystem.Substitution.apply [] binder.scheme.body) at bodySafe
    rw [Ty.apply_eq_self_of_domain_disjoint_freeVariables [] binder.scheme.body (by simp [Substitution.domain])] at bodySafe
    exact ⟨.refl _ _, safe_resolved ready bodySafe, live, new_rows_of_eq rfl⟩

  case case30 =>
    intros context expectedReturn initial fuel statement rest
      statementInduction tailInduction
    unfold InferStatementsFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    unfold inferStatementsFuel at success
    cases headResult : inferStatementFuel fuel context statement expectedReturn
        initial with
    | error error =>
        simp [headResult, bind, Except.bind] at success
    | ok head =>
        simp only [headResult, bind, Except.bind] at success
        have headProperties := inferStatementFuel_inferenceProperties ready validated canonical returnBelow headResult
        have headPrivacy := statementInduction ready wellFormed bound live catalog validated canonical returnBelow returnSafe head headResult
        cases rest with
        | nil =>
            injection success with resultEq
            rw [← resultEq]
            refine ⟨headPrivacy.1, ?_, headPrivacy.2.2.1, headPrivacy.2.2.2⟩
            split
            · exact headPrivacy.2.1
            · exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
        | cons next remaining =>
            cases tailResult : inferStatementsFuel fuel context
                (next :: remaining) expectedReturn head.state with
            | error error =>
                simp [tailResult] at success
            | ok tail =>
                simp only [tailResult] at success
                injection success with resultEq
                rw [← resultEq]
                have tailPrivacy := tailInduction head headProperties.2.1
                  ((inferStatementFuel_direct_progress headResult).wellFormed wellFormed)
                  (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) headProperties.1.next_le)
                  headPrivacy.2.2.1 catalog validated canonical
                  (returnBelow.weaken headProperties.1.next_le) (headPrivacy.1 _ returnSafe) tail tailResult
                refine ⟨headPrivacy.1.trans tailPrivacy.1, ?_, tailPrivacy.2.2.1,
                  new_requirements_trans headPrivacy.2.2.2 tailPrivacy.2.2.2 tailPrivacy.1⟩
                split
                · exact tailPrivacy.2.1
                · split
                  · exact tailPrivacy.1 _ headPrivacy.2.1
                  · exact tailPrivacy.2.1
  case case16 =>
    intro context expression expected initial fuel id allocated allocationEq callee arguments expressionEq constructorIH argumentsIH calleeIH
    apply inferExprFuel_call_private expressionEq
    · intro instantiation state
      simpa only [allocationEq] using constructorIH instantiation state
    · simpa only [allocationEq] using argumentsIH
    · exact calleeIH

  case case36 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq statementEq
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have returnAtAllocated :=
      returnBelow.weaken allocationProperties.1.next_le
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases unifyResult : Detail.unify allocated .unit expectedReturn with
    | error error =>
        simp [unifyResult] at success
    | ok unifiedState =>
        simp only [unifyResult, pure, Pure.pure, Except.pure] at success
        have unifyProgress := unify_inferenceProgress
          allocationProperties.2.solved (Ty.variablesBelow_constructor _ _)
          returnAtAllocated unifyResult
        have unifiedReady := unify_preserves_inferenceReady
          allocationProperties.2 (Ty.variablesBelow_constructor _ _)
          returnAtAllocated unifyResult
        have throughUnify := allocationProperties.1.trans unifyProgress
        have resultTypeBelow :=
          throughUnify.resolve_variablesBelow returnBelow
        have unitSafe : Safe protectedVars allocated .unit := safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
        have unifiedPrivacy := ProtectedVariables.unify unitSafe (allocationPrivacy.1 _ returnSafe) unifyResult
        have unifiedLive := allocationPrivacy.2.1.unify unitSafe (allocationPrivacy.1 _ returnSafe) unifyResult
        have returnAtUnified := safe_resolved unifiedReady (unifiedPrivacy _ (allocationPrivacy.1 _ returnSafe))
        injection success with resultEq
        rw [← resultEq]
        exact ⟨allocationPrivacy.1.trans (unifiedPrivacy.trans (.of_substitution_eq rfl)),
          SafeTransport.of_substitution_eq rfl _ returnAtUnified,
          unifiedLive.transport rfl (.of_substitution_eq rfl),
          new_rows_of_eq ((unify_requirements unifyResult).trans allocationPrivacy.2.2)⟩

  case case37 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq value statementEq valueInduction
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have returnAtAllocated :=
      returnBelow.weaken allocationProperties.1.next_le
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases valueResult : inferExprFuel fuel context value
        (some expectedReturn) allocated with
    | error error =>
        simp [valueResult] at success
    | ok valuePair =>
        rcases valuePair with ⟨inferred, valueState⟩
        simp only [valueResult, pure, Pure.pure, Except.pure] at success
        have valueProperties := inferExprFuel_inferenceProperties allocationProperties.2
          validated canonical
          (by
            intro expectedType member
            simp only [Option.mem_def] at member
            injection member with typeEq
            subst expectedType
            exact returnAtAllocated)
          valueResult
        have valuePrivacy := valueInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical
          (by
            intro type member
            simp only [Option.mem_def] at member
            injection member with same
            subst type
            exact returnAtAllocated)
          (by
            intro type member
            simp only [Option.mem_def] at member
            injection member with same
            subst type
            exact allocationPrivacy.1 _ returnSafe) _ valueResult
        have returnAtValue := safe_resolved valueProperties.2.1 (valuePrivacy.1 _ (allocationPrivacy.1 _ returnSafe))
        have prefixProgress :=
          allocationProperties.1.trans valueProperties.1
        have resultTypeBelow :=
          prefixProgress.resolve_variablesBelow returnBelow
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationPrivacy.1.trans (valuePrivacy.1.trans (.of_substitution_eq rfl)),
          SafeTransport.of_substitution_eq rfl _ returnAtValue,
          valuePrivacy.2.2.1.transport rfl (.of_substitution_eq rfl), ?_⟩
        intro row member freshRow type typeMember
        apply SafeTransport.of_substitution_eq (before := valueState) rfl
        exact valuePrivacy.2.2.2 row member (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember
  case case17 =>
    intros context expression expected initial fuel id allocated allocationEq
      dot name arguments expressionEq constructorInduction
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProperties.1.next_le
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases candidateResult : contextualConstructorCandidate context allocated
        expected name.value with
    | error error =>
        simp [candidateResult] at success
    | ok candidate =>
        rcases candidate with ⟨dataType, constructor, typeArguments⟩
        simp only [candidateResult] at success
        have instantiationBelow :=
          contextualConstructorCandidate_success_instantiation_variablesBelow
            allocationProperties.2 expectedAtAllocated validated
            candidateResult
        obtain ⟨dataMember, constructorMember, actual, expectedEq, nominalEq⟩ := contextualConstructorCandidate_success_facts candidateResult
        have instantiationSafe := contextual_constructor allocationProperties.2 validated
          (allocationPrivacy.1 _ (expectedSafe actual (by rw [expectedEq]; simp)))
          (by simpa only [expectedEq] using candidateResult)
        have finished := constructorInduction dataType constructor typeArguments allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical
          instantiationBelow.1 instantiationSafe.1 instantiationBelow.2 instantiationSafe.2
          expectedAtAllocated (fun type member => allocationPrivacy.1 _ (expectedSafe type member)) result success
        refine ⟨allocationPrivacy.1.trans finished.1, finished.2.1, finished.2.2.1, ?_⟩
        intro row member freshRow
        exact finished.2.2.2 row member (by simpa only [allocationPrivacy.2.2] using freshRow)

  case case20 =>
    intros context expression expected initial fuel id allocated allocationEq
      base dot name expressionEq constructorInduction
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProperties.1.next_le
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases candidatesResult :
        constructorCalleeCandidates context allocated expression with
    | error error =>
        simp [candidatesResult] at success
    | ok candidates =>
        simp only [candidatesResult] at success
        cases candidates with
        | nil =>
            simp only [] at success
            repeat' first | split at success
            all_goals contradiction
        | cons candidate rest =>
            cases rest with
            | cons second tail => simp at success
            | nil =>
                rcases candidate with ⟨dataType, constructor⟩
                let freshResult :=
                  freshDataConstructorInstantiation dataType constructor
                    allocated
                have candidateFacts :=
                  constructorCalleeCandidates_success_members candidatesResult
                    dataType constructor (by simp)
                have payloadTypesBelow :=
                  validated.data_constructor_payloadTypes_variablesBelow
                    candidateFacts.1 candidateFacts.2
                    allocated.inference.next
                have freshProperties :=
                  freshDataConstructorInstantiation_inferenceProperties
                    dataType constructor allocated allocationProperties.2
                    payloadTypesBelow
                have payloadClosed := validated.data_constructor_payloadTypes_variablesBelow candidateFacts.1 candidateFacts.2 0
                have freshPrivacy := fresh_constructor (dataType := dataType) allocationProperties.2 boundAllocated payloadClosed
                have freshLive := allocationPrivacy.2.1.transport
                  (congrArg LexicalScope.binders (freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor allocated)) freshPrivacy.1
                have freshWF := (freshDataConstructorInstantiation_direct_progress dataType constructor allocated).wellFormed wfAllocated
                have finished := constructorInduction freshResult.1 freshResult.2 freshProperties.2.1 freshWF
                  (fun metavariable member => Nat.lt_of_lt_of_le (boundAllocated metavariable member) freshProperties.1.next_le)
                  freshLive catalog validated canonical freshProperties.2.2.2.1 freshPrivacy.2.1
                  freshProperties.2.2.2.2 freshPrivacy.2.2
                  (fun type member => (expectedAtAllocated type member).weaken freshProperties.1.next_le)
                  (fun type member => freshPrivacy.1 _ (allocationPrivacy.1 _ (expectedSafe type member))) result
                  (by simpa only [freshResult] using success)
                refine ⟨allocationPrivacy.1.trans (freshPrivacy.1.trans finished.1), finished.2.1, finished.2.2.1, ?_⟩
                intro row member freshRow
                apply finished.2.2.2 row member
                simpa only [freshResult, freshDataConstructorInstantiation_requirements, allocationPrivacy.2.2] using freshRow

  case case70 =>
    intros fuel context target operator value initial placeIH valueIH
    unfold InferAssignedValueFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferAssignedValueFuel at success
    cases placeRun : inferPlaceFuel fuel context target initial with
    | error error => simp [placeRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨place, placeState⟩
      simp only [placeRun, bind, Except.bind] at success
      have placeProperties := inferPlaceFuel_inferenceProperties ready validated canonical placeRun
      have placePrivacy := placeIH ready wellFormed bound live catalog validated canonical _ placeRun
      have placeWF := (inferPlaceFuel_direct_progress placeRun).wellFormed wellFormed
      have finishValue (fitted : State)
          (fitProgress : placeState.InferenceProgress fitted)
          (fitReady : fitted.InferenceReady) (fitWF : fitted.RequirementsWellFormed)
          (fitPrivacy : SafeTransport protectedVars placeState fitted)
          (fitLive : LiveBindersSafe protectedVars fitted)
          (fitRows : fitted.requirements = placeState.requirements)
          (expected : Ty) (expectedBelow : expected.VariablesBelow fitted.inference.next)
          (expectedSafe : Safe protectedVars fitted expected)
          (ih : InferExprFuelPrivacy protectedVars fuel context value (some expected) fitted)
          (accepted : (do
            let (inferredValue, finalState) ← inferExprFuel fuel context value (some expected) fitted
            pure (({ target := { place with type := finalState.resolve place.type } } : AssignmentResolution), inferredValue, finalState)) = .ok result) :
          SafeTransport protectedVars initial result.2.2 ∧
            Safe protectedVars result.2.2 result.1.target.type ∧
            Safe protectedVars result.2.2 result.2.1.type ∧ LiveBindersSafe protectedVars result.2.2 ∧
            ∀ row ∈ result.2.2.requirements, row ∉ initial.requirements → PredicateSafe protectedVars result.2.2 row.predicate := by
        cases valueRun : inferExprFuel fuel context value (some expected) fitted with
        | error error => simp [valueRun, bind, Except.bind] at accepted
        | ok pair =>
          rcases pair with ⟨inferredValue, finalState⟩
          simp only [valueRun, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
          cases accepted
          have expectedBelow' : ∀ type ∈ some expected, type.VariablesBelow fitted.inference.next := by
            intro type member
            simp only [Option.mem_def] at member
            injection member with same
            subst type
            exact expectedBelow
          have valueProperties := inferExprFuel_inferenceProperties fitReady validated canonical expectedBelow' valueRun
          have valuePrivacy := ih fitReady fitWF
            (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) (placeProperties.1.trans fitProgress).next_le)
            fitLive catalog validated canonical expectedBelow' (by
              intro type member
              simp only [Option.mem_def] at member
              injection member with same
              subst type
              exact expectedSafe) _ valueRun
          have allRows := new_requirements_trans placePrivacy.2.2.2
            (new_requirements_trans (new_rows_of_eq fitRows) valuePrivacy.2.2.2 valuePrivacy.1)
            (fitPrivacy.trans valuePrivacy.1)
          exact ⟨placePrivacy.1.trans (fitPrivacy.trans valuePrivacy.1),
            safe_resolved valueProperties.2.1 (valuePrivacy.1 _ (fitPrivacy _ placePrivacy.2.1)),
            valuePrivacy.2.1, valuePrivacy.2.2.1, allRows⟩
      have finishNonEqual
          (ih : ∀ fitted, InferExprFuelPrivacy protectedVars fuel context value (some .word) fitted)
          (accepted : (do
            let fitted ← Detail.unify placeState place.type .word
            let (inferredValue, finalState) ← inferExprFuel fuel context value (some .word) fitted
            pure (({ target := { place with type := finalState.resolve place.type } } : AssignmentResolution), inferredValue, finalState)) = .ok result) :
          SafeTransport protectedVars initial result.2.2 ∧
            Safe protectedVars result.2.2 result.1.target.type ∧
            Safe protectedVars result.2.2 result.2.1.type ∧ LiveBindersSafe protectedVars result.2.2 ∧
            ∀ row ∈ result.2.2.requirements, row ∉ initial.requirements → PredicateSafe protectedVars result.2.2 row.predicate := by
        cases fittedRun : Detail.unify placeState place.type .word with
        | error error => simp [fittedRun, bind, Except.bind] at accepted
        | ok fitted =>
          simp only [fittedRun, bind, Except.bind] at accepted
          have wordSafe : Safe protectedVars placeState .word := safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
          have fittedPrivacy := ProtectedVariables.unify placePrivacy.2.1 wordSafe fittedRun
          exact finishValue fitted
            (unify_inferenceProgress placeProperties.2.1.solved placeProperties.2.2 (Ty.variablesBelow_constructor _ _) fittedRun)
            (unify_preserves_inferenceReady placeProperties.2.1 placeProperties.2.2 (Ty.variablesBelow_constructor _ _) fittedRun)
            (unify_preserves_requirementsWellFormed fittedRun placeWF) fittedPrivacy
            (placePrivacy.2.2.1.unify placePrivacy.2.1 wordSafe fittedRun) (unify_requirements fittedRun)
            .word (Ty.variablesBelow_constructor _ _) (fittedPrivacy _ wordSafe) (ih fitted) accepted
      cases operator with
      | equal =>
        simp only [pure, Pure.pure, Except.pure] at success
        exact finishValue placeState (.refl placeProperties.2.1.solved) placeProperties.2.1 placeWF
          (.refl _ _) placePrivacy.2.2.1 rfl (placeState.resolve place.type)
          (placeProperties.2.1.solved.variablesBelow_apply placeProperties.2.2)
          (safe_resolved placeProperties.2.1 placePrivacy.2.1) (valueIH place placeState) success
      | add => exact finishNonEqual (valueIH place) success
      | subtract => exact finishNonEqual (valueIH place) success
      | multiply => exact finishNonEqual (valueIH place) success
      | divide => exact finishNonEqual (valueIH place) success
      | modulo => exact finishNonEqual (valueIH place) success
      | bitAnd => exact finishNonEqual (valueIH place) success
      | bitXor => exact finishNonEqual (valueIH place) success
      | bitOr => exact finishNonEqual (valueIH place) success
  case case46 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq condition body statementEq conditionInduction bodyInduction
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    let loopContext := { context with loopDepth := context.loopDepth + 1 }
    have loopValidated :
        ProgramSignatureFormationValidated loopContext.signatures := by
      simpa only [loopContext] using validated
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases conditionResult : inferExprFuel fuel context condition (some .bool)
        allocated with
    | error error =>
        simp [conditionResult] at success
    | ok conditionPair =>
      rcases conditionPair with ⟨inferredCondition, conditionState⟩
      simp only [conditionResult] at success
      have conditionProperties := inferExprFuel_inferenceProperties allocationProperties.2
        validated canonical
        (by
          intro expectedType member
          simp at member
          subst expectedType
          exact Ty.variablesBelow_constructor _ _)
        conditionResult
      have conditionPrivacy := conditionInduction allocationProperties.2 wfAllocated boundAllocated
        allocationPrivacy.2.1 catalog validated canonical
        (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
        (by intro type member; cases Option.mem_def.mp member; exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _))
        _ conditionResult
      have throughCondition :=
        allocationProperties.1.trans conditionProperties.1
      cases bodyResult : inferStatementsFuel fuel loopContext body.value
          expectedReturn conditionState with
      | error error =>
          simp [loopContext, bodyResult] at success
      | ok inferredBody =>
        simp only [loopContext, bodyResult] at success
        have bodyPrivacy := bodyInduction conditionState conditionProperties.2.1
          ((inferExprFuel_direct_progress conditionResult).wellFormed wfAllocated)
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughCondition.next_le)
          conditionPrivacy.2.2.1 catalog validated canonical
          (returnBelow.weaken throughCondition.next_le)
          (conditionPrivacy.1 _ (allocationPrivacy.1 _ returnSafe)) _ bodyResult
        have restoredLive := conditionPrivacy.2.2.1.restore bodyPrivacy.1
        injection success with resultEq
        rw [← resultEq]
        refine ⟨allocationPrivacy.1.trans (conditionPrivacy.1.trans (bodyPrivacy.1.trans (.of_substitution_eq rfl))),
          safe_closed _ _ (Ty.variablesBelow_constructor 0 _),
          restoredLive.transport rfl (.of_substitution_eq rfl), ?_⟩
        have rows := new_requirements_trans conditionPrivacy.2.2.2 bodyPrivacy.2.2.2 bodyPrivacy.1
        intro row member freshRow type typeMember
        apply SafeTransport.of_substitution_eq (before := inferredBody.state) rfl
        exact rows row member (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember

  case case43 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq scrutinees arms form
    dsimp only
    intro source single casesIH bodyIH sourceIH
    apply inferStatementFuel_match_single_private form single casesIH bodyIH
    simpa only [allocationEq] using sourceIH
  case case44 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq scrutinees arms form
    dsimp only
    intro notSingleton casesIH bodyIH sourcesIH
    apply inferStatementFuel_match_many_private form notSingleton casesIH bodyIH
    simpa only [allocationEq] using sourcesIH
  case case45 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq headerSpan initializer condition post body form initializerIH conditionIH bodyIH postIH
    apply inferStatementFuel_for_private form
    · simpa only [allocationEq] using initializerIH
    · exact conditionIH
    · exact bodyIH
    · exact postIH
  case case19 =>
    intros context expression expected initial fuel id allocated allocationEq
      base brackets index expressionEq baseInduction indexInduction
    unfold InferExprFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases baseResult : inferExprFuel fuel context base none allocated with
    | error error =>
        simp [baseResult] at success
    | ok basePair =>
        rcases basePair with ⟨inferredBase, baseState⟩
        simp only [baseResult] at success
        have baseProperties := inferExprFuel_inferenceProperties allocationProperties.2 validated canonical (by simp) baseResult
        have basePrivacy := baseInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1 catalog validated canonical (by simp) (by simp) _ baseResult
        have baseWF := (inferExprFuel_direct_progress baseResult).wellFormed wfAllocated
        have baseBound : ∀ metavariable ∈ protectedVars, metavariable.index < baseState.inference.next :=
          fun metavariable member => Nat.lt_of_lt_of_le (boundAllocated metavariable member) baseProperties.1.next_le
        let keyAllocation := baseState.fresh
        have keyProperties := fresh_eq_inferenceProperties
          baseProperties.2.1 (type := keyAllocation.1)
          (next := keyAllocation.2) rfl
        let valueAllocation := keyAllocation.2.fresh
        have valueProperties := fresh_eq_inferenceProperties
          keyProperties.2.1 (type := valueAllocation.1)
          (next := valueAllocation.2) rfl
        have baseAtValue : inferredBase.type.VariablesBelow
            valueAllocation.2.inference.next :=
          baseProperties.2.2.weaken
            (keyProperties.1.trans valueProperties.1).next_le
        have keyAtValue : keyAllocation.1.VariablesBelow
            valueAllocation.2.inference.next :=
          keyProperties.2.2.weaken valueProperties.1.next_le
        have mappingBelow :
            (Ty.mapping keyAllocation.1 valueAllocation.1).VariablesBelow
              valueAllocation.2.inference.next :=
          (Ty.variablesBelow_mapping_iff _ _ _).2
            ⟨keyAtValue, valueProperties.2.2⟩
        have twoFresh : SafeTransport protectedVars baseState valueAllocation.2 := fresh.trans fresh
        have keySafe : Safe protectedVars valueAllocation.2 keyAllocation.1 := fresh _ (fresh_type baseProperties.2.1 baseBound)
        have valueSafe : Safe protectedVars valueAllocation.2 valueAllocation.1 :=
          fresh_type keyProperties.2.1 (by
            intro metavariable member
            exact Nat.lt_of_lt_of_le (baseBound metavariable member) keyProperties.1.next_le)
        have baseSafe := twoFresh _ basePrivacy.2.1
        have mappingSafe := (safe_mapping_iff _ _ _ _).mpr ⟨keySafe, valueSafe⟩
        have freshLive := basePrivacy.2.2.1.transport (after := valueAllocation.2) rfl twoFresh
        cases unifyResult : Detail.unify valueAllocation.2 inferredBase.type
            (.mapping keyAllocation.1 valueAllocation.1) with
        | error error =>
            simp [keyAllocation, valueAllocation, unifyResult] at success
        | ok unifiedState =>
            simp only [keyAllocation, valueAllocation, unifyResult] at success
            have unifyProgress := unify_inferenceProgress
              valueProperties.2.1.solved baseAtValue mappingBelow unifyResult
            have unifiedReady := unify_preserves_inferenceReady
              valueProperties.2.1 baseAtValue mappingBelow unifyResult
            have unifiedPrivacy := ProtectedVariables.unify baseSafe mappingSafe unifyResult
            have toUnified := twoFresh.trans unifiedPrivacy
            have unifiedLive := freshLive.unify baseSafe mappingSafe unifyResult
            have unifiedWF := unify_preserves_requirementsWellFormed unifyResult baseWF
            have beforeKeyRows := new_requirements_trans basePrivacy.2.2.2
              (new_rows_of_eq (show unifiedState.requirements = baseState.requirements from unify_requirements (state := valueAllocation.2) unifyResult)) toUnified
            have keySafeAtUnified := safe_resolved unifiedReady (unifiedPrivacy _ keySafe)
            have keyAtUnified : keyAllocation.1.VariablesBelow
                unifiedState.inference.next :=
              keyAtValue.weaken unifyProgress.next_le
            have resolvedKeyBelow :
                (unifiedState.resolve keyAllocation.1).VariablesBelow
                  unifiedState.inference.next :=
              unifiedReady.solved.variablesBelow_apply keyAtUnified
            cases indexResult : inferExprFuel fuel context index
                (some (unifiedState.resolve baseState.fresh.1))
                unifiedState with
            | error error =>
                simp [indexResult] at success
            | ok indexPair =>
                rcases indexPair with ⟨inferredIndex, indexState⟩
                simp only [indexResult]
                  at success
                have indexProperties := inferExprFuel_inferenceProperties unifiedReady validated canonical
                  (by
                    intro expectedType member
                    simp only [Option.mem_def] at member
                    injection member with typeEq
                    subst expectedType
                    simpa only [keyAllocation] using resolvedKeyBelow)
                  indexResult
                have keyPrivacy := indexInduction baseState.fresh.1 unifiedState unifiedReady unifiedWF
                  (fun metavariable member => Nat.lt_of_lt_of_le (baseBound metavariable member)
                    (keyProperties.1.trans (valueProperties.1.trans unifyProgress)).next_le)
                  unifiedLive catalog validated canonical
                  (by
                    intro type member
                    cases Option.mem_def.mp member
                    exact resolvedKeyBelow)
                  (by
                    intro type member
                    cases Option.mem_def.mp member
                    exact keySafeAtUnified) _ indexResult
                have allRows := new_requirements_trans beforeKeyRows keyPrivacy.2.2.2 keyPrivacy.1
                have finalValueSafe := safe_resolved indexProperties.2.1 (keyPrivacy.1 _ (unifiedPrivacy _ valueSafe))
                have fromValueToIndex :=
                  unifyProgress.trans indexProperties.1
                have resolvedValueBelow :=
                  fromValueToIndex.resolve_variablesBelow
                    valueProperties.2.2
                have prefixProgress := allocationProperties.1.trans
                  (baseProperties.1.trans
                    (keyProperties.1.trans
                      (valueProperties.1.trans fromValueToIndex)))
                have expectedAtIndex : ∀ expectedType ∈ expected,
                    expectedType.VariablesBelow indexState.inference.next := by
                  intro expectedType member
                  exact (expectedBelow expectedType member).weaken
                    prefixProgress.next_le
                have toIndex := allocationPrivacy.1.trans (basePrivacy.1.trans (toUnified.trans keyPrivacy.1))
                have recorded := recordExpressionWithExpected_private catalog indexProperties.2.1 resolvedValueBelow expectedAtIndex
                  finalValueSafe (fun type member => toIndex _ (expectedSafe type member)) keyPrivacy.2.2.1 success
                refine ⟨toIndex.trans recorded.1, recorded.2.1, recorded.2.2.1, ?_⟩
                intro row member freshRow
                exact new_requirements_trans allRows recorded.2.2.2 recorded.1 row member
                  (by simpa only [allocationPrivacy.2.2] using freshRow)

  case case68 =>
    intros context target initial fuel base brackets key targetEq
      baseInduction keyInduction
    unfold InferPlaceFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical result success
    unfold inferPlaceFuel at success
    simp only [targetEq, bind, Except.bind] at success
    cases baseResult : inferPlaceFuel fuel context base initial with
    | error error =>
        simp [baseResult] at success
    | ok basePair =>
        rcases basePair with ⟨basePlace, baseState⟩
        simp only [baseResult] at success
        have baseProperties := inferPlaceFuel_inferenceProperties ready validated canonical baseResult
        have basePrivacy := baseInduction ready wellFormed bound live catalog validated canonical _ baseResult
        have baseWF := (inferPlaceFuel_direct_progress baseResult).wellFormed wellFormed
        have baseBound : ∀ metavariable ∈ protectedVars, metavariable.index < baseState.inference.next :=
          fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) baseProperties.1.next_le
        let keyAllocation := baseState.fresh
        have keyProperties := fresh_eq_inferenceProperties
          baseProperties.2.1 (type := keyAllocation.1)
          (next := keyAllocation.2) rfl
        let valueAllocation := keyAllocation.2.fresh
        have valueProperties := fresh_eq_inferenceProperties
          keyProperties.2.1 (type := valueAllocation.1)
          (next := valueAllocation.2) rfl
        have baseAtValue : basePlace.type.VariablesBelow
            valueAllocation.2.inference.next :=
          baseProperties.2.2.weaken
            (keyProperties.1.trans valueProperties.1).next_le
        have keyAtValue : keyAllocation.1.VariablesBelow
            valueAllocation.2.inference.next :=
          keyProperties.2.2.weaken valueProperties.1.next_le
        have mappingBelow :
            (Ty.mapping keyAllocation.1 valueAllocation.1).VariablesBelow
              valueAllocation.2.inference.next :=
          (Ty.variablesBelow_mapping_iff _ _ _).2
            ⟨keyAtValue, valueProperties.2.2⟩
        have twoFresh : SafeTransport protectedVars baseState valueAllocation.2 := fresh.trans fresh
        have keySafe : Safe protectedVars valueAllocation.2 keyAllocation.1 := fresh _ (fresh_type baseProperties.2.1 baseBound)
        have valueSafe : Safe protectedVars valueAllocation.2 valueAllocation.1 :=
          fresh_type keyProperties.2.1 (by
            intro metavariable member
            exact Nat.lt_of_lt_of_le (baseBound metavariable member) keyProperties.1.next_le)
        have baseSafe := twoFresh _ basePrivacy.2.1
        have mappingSafe := (safe_mapping_iff _ _ _ _).mpr ⟨keySafe, valueSafe⟩
        have freshLive := basePrivacy.2.2.1.transport (after := valueAllocation.2) rfl twoFresh
        cases unifyResult : Detail.unify valueAllocation.2 basePlace.type
            (.mapping keyAllocation.1 valueAllocation.1) with
        | error error =>
            simp [keyAllocation, valueAllocation, unifyResult] at success
        | ok unifiedState =>
            simp only [keyAllocation, valueAllocation, unifyResult] at success
            have unifyProgress := unify_inferenceProgress
              valueProperties.2.1.solved baseAtValue mappingBelow unifyResult
            have unifiedReady := unify_preserves_inferenceReady
              valueProperties.2.1 baseAtValue mappingBelow unifyResult
            have unifiedPrivacy := ProtectedVariables.unify baseSafe mappingSafe unifyResult
            have toUnified := twoFresh.trans unifiedPrivacy
            have unifiedLive := freshLive.unify baseSafe mappingSafe unifyResult
            have unifiedWF := unify_preserves_requirementsWellFormed unifyResult baseWF
            have beforeKeyRows := new_requirements_trans basePrivacy.2.2.2
              (new_rows_of_eq (show unifiedState.requirements = baseState.requirements from unify_requirements (state := valueAllocation.2) unifyResult)) toUnified
            have keySafeAtUnified := safe_resolved unifiedReady (unifiedPrivacy _ keySafe)
            have keyAtUnified : keyAllocation.1.VariablesBelow
                unifiedState.inference.next :=
              keyAtValue.weaken unifyProgress.next_le
            have resolvedKeyBelow :
                (unifiedState.resolve keyAllocation.1).VariablesBelow
                  unifiedState.inference.next :=
              unifiedReady.solved.variablesBelow_apply keyAtUnified
            cases keyResult : inferExprFuel fuel context key
                (some (unifiedState.resolve baseState.fresh.1)) unifiedState with
            | error error =>
                simp [keyResult] at success
            | ok keyPair =>
                rcases keyPair with ⟨inferredKey, keyState⟩
                simp only [keyResult, pure, Pure.pure, Except.pure] at success
                injection success with resultEq
                rw [← resultEq]
                have keyExpressionProperties := inferExprFuel_inferenceProperties unifiedReady validated canonical
                  (by
                    intro expectedType member
                    simp only [Option.mem_def] at member
                    injection member with typeEq
                    subst expectedType
                    simpa only [keyAllocation] using resolvedKeyBelow)
                  keyResult
                have keyPrivacy := keyInduction baseState.fresh.1 unifiedState unifiedReady unifiedWF
                  (fun metavariable member => Nat.lt_of_lt_of_le (baseBound metavariable member)
                    (keyProperties.1.trans (valueProperties.1.trans unifyProgress)).next_le)
                  unifiedLive catalog validated canonical
                  (by
                    intro type member
                    cases Option.mem_def.mp member
                    exact resolvedKeyBelow)
                  (by
                    intro type member
                    cases Option.mem_def.mp member
                    exact keySafeAtUnified) _ keyResult
                have allRows := new_requirements_trans beforeKeyRows keyPrivacy.2.2.2 keyPrivacy.1
                have finalValueSafe := safe_resolved keyExpressionProperties.2.1 (keyPrivacy.1 _ (unifiedPrivacy _ valueSafe))
                have fromValueToKey :=
                  unifyProgress.trans keyExpressionProperties.1
                have resolvedValueBelow :=
                  fromValueToKey.resolve_variablesBelow
                    valueProperties.2.2
                exact ⟨basePrivacy.1.trans (toUnified.trans keyPrivacy.1), finalValueSafe, keyPrivacy.2.2.1, allRows⟩
  case case39 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq condition thenBody elseBody statementEq
      conditionInduction thenInduction elseInduction
    unfold InferStatementFuelPrivacy
    intro ready wellFormed bound live catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have boundAllocated : ∀ metavariable ∈ protectedVars, metavariable.index < allocated.inference.next := by
      intro metavariable member
      rw [allocatedEq]
      change metavariable.index < initial.inference.next
      exact bound metavariable member
    have wfAllocated : allocated.RequirementsWellFormed := by
      rw [allocatedEq]
      change initial.RequirementsWellFormed
      exact wellFormed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases conditionResult : inferExprFuel fuel context condition (some .bool)
        allocated with
    | error error =>
        simp [conditionResult] at success
    | ok conditionPair =>
        rcases conditionPair with ⟨inferredCondition, conditionState⟩
        simp only [conditionResult] at success
        have conditionProperties := inferExprFuel_inferenceProperties allocationProperties.2
          validated canonical
          (by
            intro expectedType member
            simp only [Option.mem_def] at member
            injection member with typeEq
            subst expectedType
            exact Ty.variablesBelow_constructor _ _)
          conditionResult
        have conditionPrivacy := conditionInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical
          (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
          (by intro type member; cases Option.mem_def.mp member; exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)) _ conditionResult
        have toCondition := allocationPrivacy.1.trans conditionPrivacy.1
        have conditionWF := (inferExprFuel_direct_progress conditionResult).wellFormed wfAllocated
        have throughCondition :=
          allocationProperties.1.trans conditionProperties.1
        cases thenResultEq : inferStatementsFuel fuel context thenBody.value
            expectedReturn conditionState with
        | error error =>
            simp [thenResultEq] at success
        | ok thenResult =>
            simp only [thenResultEq] at success
            have thenProperties := inferStatementsFuel_inferenceProperties conditionProperties.2.1 validated canonical
              (returnBelow.weaken throughCondition.next_le) thenResultEq
            have thenPrivacy := thenInduction conditionState conditionProperties.2.1 conditionWF
              (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughCondition.next_le)
              conditionPrivacy.2.2.1 catalog validated canonical
              (returnBelow.weaken throughCondition.next_le) (toCondition _ returnSafe) _ thenResultEq
            let afterThen := thenResult.state.restoreLexicalScope
              conditionState.lexicalScope
            have restoredThen :
                conditionState.InferenceProgress afterThen ∧
                  afterThen.InferenceReady := by
              simpa only [afterThen] using
                State.restoreLexicalScope_inferenceProperties
                  conditionProperties.2.1 thenProperties.1
            have restorePrivacy : SafeTransport protectedVars thenResult.state afterThen := .of_substitution_eq rfl
            have restoredLive : LiveBindersSafe protectedVars afterThen := conditionPrivacy.2.2.1.restore thenPrivacy.1
            have thenWF := (inferStatementsFuel_direct_progress thenResultEq).wellFormed conditionWF
            have toRestored := toCondition.trans (thenPrivacy.1.trans restorePrivacy)
            have bodyRows := new_requirements_trans conditionPrivacy.2.2.2 thenPrivacy.2.2.2 thenPrivacy.1
            have restoredRows : ∀ row ∈ afterThen.requirements, row ∉ allocated.requirements → PredicateSafe protectedVars afterThen row.predicate := by
              intro row member freshRow type typeMember
              exact restorePrivacy _ (bodyRows row member freshRow type typeMember)
            cases elseBody with
            | none =>
                simp only [pure, Pure.pure, Except.pure] at success
                injection success with resultEq
                rw [← resultEq]
                refine ⟨toRestored.trans (.of_substitution_eq rfl),
                  safe_closed _ _ (Ty.variablesBelow_constructor 0 _),
                  restoredLive.transport rfl (.of_substitution_eq rfl), ?_⟩
                intro row member freshRow type typeMember
                apply SafeTransport.of_substitution_eq (before := afterThen) rfl
                exact restoredRows row member (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember
            | some elseBody =>
                cases elseResultEq : inferStatementsFuel fuel context
                    elseBody.value expectedReturn afterThen with
                | error error =>
                    simp [afterThen, elseResultEq]
                      at success
                | ok elseResult =>
                    simp only [afterThen, elseResultEq, pure, Pure.pure, Except.pure] at success
                    have elseProperties := inferStatementsFuel_inferenceProperties restoredThen.2 validated canonical
                      (returnBelow.weaken
                        (throughCondition.trans restoredThen.1).next_le)
                      elseResultEq
                    have elsePrivacy := elseInduction conditionState thenResult elseBody restoredThen.2
                      (State.restoreLexicalScope_preserves_requirementsWellFormed _ _ thenWF)
                      (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) (throughCondition.trans restoredThen.1).next_le)
                      restoredLive catalog validated canonical
                      (returnBelow.weaken (throughCondition.trans restoredThen.1).next_le)
                      (toRestored _ returnSafe) _ elseResultEq
                    have toElse := toRestored.trans elsePrivacy.1
                    have finalLive := conditionPrivacy.2.2.1.restore (thenPrivacy.1.trans (restorePrivacy.trans elsePrivacy.1))
                    have elseRows := new_requirements_trans restoredRows elsePrivacy.2.2.2 elsePrivacy.1
                    have resolvedReturnSafe := safe_resolved elseProperties.2.1 (toElse _ returnSafe)
                    have restoredElse :=
                      State.restoreLexicalScope_inferenceProperties
                        conditionProperties.2.1
                        (restoredThen.1.trans elseProperties.1)
                    have throughElse :=
                      throughCondition.trans restoredElse.1
                    injection success with resultEq
                    rw [← resultEq]
                    refine ⟨toElse.trans (.of_substitution_eq rfl), ?_,
                      finalLive.transport rfl (.of_substitution_eq rfl), ?_⟩
                    · split
                      · exact SafeTransport.of_substitution_eq rfl _ resolvedReturnSafe
                      · exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
                    · intro row member freshRow type typeMember
                      apply SafeTransport.of_substitution_eq (before := elseResult.state) rfl
                      exact elseRows row member (by simpa only [allocationPrivacy.2.2] using freshRow) type typeMember


/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferExprFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context expression expected state,
      InferExprFuelPrivacy protectedVars fuel context expression expected state :=
  (inferFuel_privacy_internal protectedVars).1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferConstructorApplicationFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelPrivacy protectedVars fuel context source id instantiation arguments expected state :=
  (inferFuel_privacy_internal protectedVars).2.1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferConstructorArgumentsFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context sources expected state,
      InferConstructorArgumentsFuelPrivacy protectedVars fuel context sources expected state :=
  (inferFuel_privacy_internal protectedVars).2.2.1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferStatementsFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context statements expectedReturn state,
      InferStatementsFuelPrivacy protectedVars fuel context statements expectedReturn state :=
  (inferFuel_privacy_internal protectedVars).2.2.2.1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferStatementFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context statement expectedReturn state,
      InferStatementFuelPrivacy protectedVars fuel context statement expectedReturn state :=
  (inferFuel_privacy_internal protectedVars).2.2.2.2.1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferForItemsFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context items state,
      InferForItemsFuelPrivacy protectedVars fuel context items state :=
  (inferFuel_privacy_internal protectedVars).2.2.2.2.2.1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferForItemFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context item state,
      InferForItemFuelPrivacy protectedVars fuel context item state :=
  (inferFuel_privacy_internal protectedVars).2.2.2.2.2.2.1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferPlaceFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context target state,
      InferPlaceFuelPrivacy protectedVars fuel context target state :=
  (inferFuel_privacy_internal protectedVars).2.2.2.2.2.2.2.1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferAssignedValueFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context target operator value state,
      InferAssignedValueFuelPrivacy protectedVars fuel context target operator value state :=
  (inferFuel_privacy_internal protectedVars).2.2.2.2.2.2.2.2.1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferExprsFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context expressions state,
      InferExprsFuelPrivacy protectedVars fuel context expressions state :=
  (inferFuel_privacy_internal protectedVars).2.2.2.2.2.2.2.2.2.1

/-- Privacy follows the actual successful inference call and its recursive children. -/
theorem inferMatchCasesFuel_private (protectedVars : List TypeVarId) :
    ∀ fuel context scrutineeType expectedReturn outerScope cases state,
      InferMatchCasesFuelPrivacy protectedVars fuel context scrutineeType expectedReturn outerScope cases state :=
  (inferFuel_privacy_internal protectedVars).2.2.2.2.2.2.2.2.2.2

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
