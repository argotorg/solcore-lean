import Solcore.SourceSemantics.SourceInferenceProtectedVariableMatchStatement
import Solcore.SourceSemantics.SourceInferenceProtectedVariableConstructorContinuation
import Solcore.SourceSemantics.SourceInferenceProtectedVariableForContinuation
import Solcore.SourceSemantics.SourceInferenceProtectedVariableMatchContinuation
import Solcore.SourceSemantics.SourceInferenceProtectedVariableLocalLookup
import Solcore.SourceSemantics.SourceInferenceProtectedVariableOperators
import Solcore.SourceSemantics.SourceInferenceProtectedVariableCallRecording
import Solcore.SourceSemantics.SourceInferenceProtectedVariablePatterns
import Solcore.SourceSemantics.SourceInferenceProtectedVariableLambda

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


private theorem builtinFunction_type_closed (function : BuiltinFunctionId) :
    function.type.VariablesBelow 0 := by
  unfold BuiltinFunctionId.type
  apply (Ty.variablesBelow_function_iff _ _ _).mpr
  constructor
  · apply Ty.variablesBelow_productMany
    cases function <;> simp [BuiltinFunctionId.parameterTypes, Ty.integer, Ty.word]
  · cases function <;> simp [BuiltinFunctionId.returnType, Ty.integer, Ty.word, Ty.bool]

set_option maxHeartbeats 2000000 in
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

private theorem inferFuel_fixedness_internal (protectedVars : List TypeVarId) :
    (∀ fuel context expression expected state,
      InferExprFuelFixedness protectedVars fuel context expression expected state) ∧
    (∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelFixedness protectedVars fuel context source id
        instantiation arguments expected state) ∧
    (∀ fuel context sources expected state,
      InferConstructorArgumentsFuelFixedness protectedVars fuel context sources
        expected state) ∧
    (∀ fuel context statements expectedReturn state,
      InferStatementsFuelFixedness protectedVars fuel context statements
        expectedReturn state) ∧
    (∀ fuel context statement expectedReturn state,
      InferStatementFuelFixedness protectedVars fuel context statement
        expectedReturn state) ∧
    (∀ fuel context items state,
      InferForItemsFuelFixedness protectedVars fuel context items state) ∧
    (∀ fuel context item state,
      InferForItemFuelFixedness protectedVars fuel context item state) ∧
    (∀ fuel context target state,
      InferPlaceFuelFixedness protectedVars fuel context target state) ∧
    (∀ fuel context target operator value state,
      InferAssignedValueFuelFixedness protectedVars fuel context target operator
        value state) ∧
    (∀ fuel context expressions state,
      InferExprsFuelFixedness protectedVars fuel context expressions state) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      InferMatchCasesFuelFixedness protectedVars fuel context scrutineeType
        expectedReturn outerScope cases state) := by
  apply inferExprFuel.mutual_induct
    (motive1 := InferExprFuelFixedness protectedVars)
    (motive2 := InferConstructorApplicationFuelFixedness protectedVars)
    (motive3 := InferConstructorArgumentsFuelFixedness protectedVars)
    (motive4 := InferStatementsFuelFixedness protectedVars)
    (motive5 := InferStatementFuelFixedness protectedVars)
    (motive6 := InferForItemsFuelFixedness protectedVars)
    (motive7 := InferForItemFuelFixedness protectedVars)
    (motive8 := InferPlaceFuelFixedness protectedVars)
    (motive9 := InferAssignedValueFuelFixedness protectedVars)
    (motive10 := InferExprsFuelFixedness protectedVars)
    (motive11 := InferMatchCasesFuelFixedness protectedVars)
  case case1 =>
    simp [InferExprFuelFixedness, inferExprFuel]
  case case3 =>
    simp_all [InferExprFuelFixedness, inferExprFuel, bind,
      Except.bind]
  case case5 =>
    simp_all [InferExprFuelFixedness, inferExprFuel, bind,
      Except.bind]
  case case6 =>
    simp_all [InferExprFuelFixedness, inferExprFuel]

  case case21 =>
    simp_all [InferExprFuelFixedness, inferExprFuel]
  case case22 =>
    simp_all [InferExprFuelFixedness, inferExprFuel]
  case case24 =>
    simp_all [InferConstructorApplicationFuelFixedness,
      inferConstructorApplicationFuel, bind, Except.bind]
  case case27 =>
    simp_all [InferConstructorArgumentsFuelFixedness,
      inferConstructorArgumentsFuel]
  case case28 =>
    simp [InferStatementsFuelFixedness, inferStatementsFuel]
  case case31 =>
    simp [InferStatementFuelFixedness, inferStatementFuel]
  case case32 =>
    simp_all [InferStatementFuelFixedness, inferStatementFuel,
      bind, Except.bind]
  case case47 =>
    simp_all [InferStatementFuelFixedness, inferStatementFuel]
  case case48 =>
    simp_all [InferStatementFuelFixedness, inferStatementFuel]
  case case50 =>
    simp_all [InferStatementFuelFixedness, inferStatementFuel]
  case case52 =>
    simp_all [InferStatementFuelFixedness, inferStatementFuel]
  case case55 =>
    simp [InferForItemFuelFixedness, inferForItemFuel]
  case case56 =>
    simp_all [InferForItemFuelFixedness, inferForItemFuel, bind,
      Except.bind]
  case case63 =>
    simp [InferPlaceFuelFixedness, inferPlaceFuel]
  case case65 =>
    simp_all [InferPlaceFuelFixedness, inferPlaceFuel]
  case case66 =>
    simp_all [InferPlaceFuelFixedness, inferPlaceFuel]
  case case69 =>
    simp_all [InferPlaceFuelFixedness, inferPlaceFuel]
  case case71 =>
    simp [InferExprsFuelFixedness, inferExprsFuel]
  case case74 =>
    simp [InferMatchCasesFuelFixedness, inferMatchCasesFuel]
  case case25 =>
    intros fuel context initial
    unfold InferConstructorArgumentsFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical below safe result success
    unfold inferConstructorArgumentsFuel at success
    injection success with resultEq
    subst result
    exact fixed
  case case29 =>
    intros context expectedReturn initial fuel
    unfold InferStatementsFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical below safe result success
    unfold inferStatementsFuel at success
    injection success with resultEq
    subst result
    exact fixed
  case case53 =>
    intros fuel context initial
    unfold InferForItemsFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
    unfold inferForItemsFuel at success
    injection success with resultEq
    subst result
    exact fixed
  case case72 =>
    intros context initial fuel
    unfold InferExprsFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
    unfold inferExprsFuel at success
    injection success with resultEq
    subst result
    exact fixed
  case case75 =>
    intros context scrutineeType expectedReturn outerScope initial fuel
    unfold InferMatchCasesFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical scrutineeBelow scrutineeSafe returnBelow returnSafe scopeEq result success
    unfold inferMatchCasesFuel at success
    injection success with resultEq
    subst result
    exact fixed
  case case7 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq binder lookupEq localSchemeInstantiationStart
      instantiated inference advanced predicates requirements recorded requirementsEq
    unfold InferExprFuelFixedness
    intro ready _ bound live fixed _ _ _ _ expectedSafe result success
    exact LocalVariableFrame.inferExprFuel_local_fixes_protected expressionEq allocationEq lookupEq
      success ready bound live fixed expectedSafe
  case case26 =>
    intros fuel context source sources expected expectedTypes initial sourceIH tailIH
    unfold InferConstructorArgumentsFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
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
        have sourcePrivacy := inferExprFuel_private protectedVars fuel context source (some (initial.resolve expected)) initial ready wellFormed bound live catalog validated canonical
          fitBelow fitSafe _ sourceRun
        have sourceFixed := sourceIH ready wellFormed bound live fixed catalog validated canonical
          fitBelow fitSafe _ sourceRun
        have tailFixed := tailIH sourceState sourceProperties.2.1
          ((inferExprFuel_direct_progress sourceRun).wellFormed wellFormed)
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) sourceProperties.1.next_le)
          sourcePrivacy.2.2.1 sourceFixed catalog validated canonical
          (fun type member => (expectedBelow type (by simp [member])).weaken sourceProperties.1.next_le)
          (fun type member => sourcePrivacy.1 _ (expectedSafe type (by simp [member]))) _ tailRun
        exact tailFixed
  case case54 =>
    intros fuel context item items initial itemIH tailIH
    unfold InferForItemsFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
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
        have itemPrivacy := inferForItemFuel_private protectedVars fuel context item initial ready wellFormed bound live catalog validated canonical _ itemRun
        have itemFixed := itemIH ready wellFormed bound live fixed catalog validated canonical _ itemRun
        have tailFixed := tailIH itemState itemProperties.2
          ((inferForItemFuel_direct_progress itemRun).wellFormed wellFormed)
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) itemProperties.1.next_le)
          itemPrivacy.2.1 itemFixed catalog validated canonical tail tailRun
        exact tailFixed
  case case73 =>
    intros context initial fuel expression rest expressionIH tailIH
    unfold InferExprsFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
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
        have expressionPrivacy := inferExprFuel_private protectedVars fuel context expression none initial ready wellFormed bound live catalog validated canonical
          (by simp) (by simp) _ expressionRun
        have expressionFixed := expressionIH ready wellFormed bound live fixed catalog validated canonical
          (by simp) (by simp) _ expressionRun
        have tailFixed := tailIH expressionState expressionProperties.2.1
          ((inferExprFuel_direct_progress expressionRun).wellFormed wellFormed)
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) expressionProperties.1.next_le)
          expressionPrivacy.2.2.1 expressionFixed catalog validated canonical _ tailRun
        exact tailFixed
  case case64 =>
    intros context target initial fuel name targetEq binder lookupEq monomorphic
    unfold InferPlaceFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
    unfold inferPlaceFuel at success
    simp only [targetEq, lookupEq, monomorphic, if_true] at success
    injection success with resultEq
    subst result
    exact fixed
  case case67 =>
    intros context target initial fuel inner targetEq innerIH
    unfold InferPlaceFuelFixedness at *
    intro ready wellFormed bound live fixed catalog validated canonical result success
    apply innerIH ready wellFormed bound live fixed catalog validated canonical result
    simpa only [inferPlaceFuel, targetEq] using success
  case case60 =>
    intros context item initial fuel expression itemEq expressionInduction
    unfold InferForItemFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
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
        have childFixed := expressionInduction ready wellFormed bound live fixed catalog validated
          canonical (by simp) (by simp) (inferred, expressionState) expressionResult
        exact childFixed
  case case57 =>
    intros context item initial fuel name sourceType itemEq
    unfold InferForItemFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
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
        injection success with resultEq
        rw [← resultEq]
        exact fixed.of_substitution_eq rfl
  case case33 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq name sourceType statementEq
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        injection success with resultEq
        rw [← resultEq]
        exact fixedAllocated.of_substitution_eq rfl
  case case34 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq name initializer statementEq initializerInduction
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have initializerFixed := initializerInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 fixedAllocated catalog validated canonical (by simp) (by simp) _ initializerResult
        let binding :=
          let locals := initializerState.binderEnvironment.apply
            initializerState.inference.substitution
          let valueType := initializerState.resolve inferred.type
          let generalized := generalizeValue initializerState locals
            allocated.nextRequirement valueType
          (initializerState.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        injection success with resultEq
        rw [← resultEq]
        exact initializerFixed.of_substitution_eq rfl
  case case35 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq name sourceType initializer statementEq
      initializerInduction
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
            have initializerFixed := initializerInduction resolvedType allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1 fixedAllocated catalog validated canonical
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
            injection success with resultEq
            rw [← resultEq]
            exact initializerFixed.of_substitution_eq rfl
  case case58 =>
    intros context item initial fuel name initializer itemEq
      initializerInduction
    unfold InferForItemFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
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
        have initializerFixed := initializerInduction ready wellFormed bound live fixed catalog validated canonical
          (by simp) (by simp) _ initializerResult
        let binding :=
          let locals := initializerState.binderEnvironment.apply
            initializerState.inference.substitution
          let valueType := initializerState.resolve inferred.type
          let generalized := generalizeValue initializerState locals
            initial.nextRequirement valueType
          (initializerState.withLocals locals).allocateBinder name.value
            generalized.scheme (some name.span) false generalized.requirements
        injection success with resultEq
        rw [← resultEq]
        exact initializerFixed.of_substitution_eq rfl
  case case59 =>
    intros context item initial fuel name sourceType initializer itemEq
      initializerInduction
    unfold InferForItemFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
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
            have initializerFixed := initializerInduction resolvedType ready wellFormed bound live fixed catalog validated canonical
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
            injection success with resultEq
            rw [← resultEq]
            exact initializerFixed.of_substitution_eq rfl
  case case37 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq value statementEq valueInduction
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have returnAtAllocated :=
      returnBelow.weaken allocationProperties.1.next_le
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have childFixed := valueInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 fixedAllocated catalog validated canonical
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
        injection success with resultEq
        rw [← resultEq]
        exact childFixed.of_substitution_eq rfl
  case case38 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq expression trailingSemicolon statementEq
      expressionInduction
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have childFixed := expressionInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 fixedAllocated catalog validated canonical (by simp) (by simp) _ expressionResult
        injection success with resultEq
        rw [← resultEq]
        exact childFixed.of_substitution_eq rfl
  case case40 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq body statementEq bodyInduction
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have childFixed := bodyInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 fixedAllocated catalog validated canonical
          (returnBelow.weaken allocationProperties.1.next_le) (allocationPrivacy.1 _ returnSafe) _ bodyResultEq
        injection success with resultEq
        rw [← resultEq]
        exact childFixed.of_substitution_eq rfl
  case case41 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq target operator value statementEq assignmentInduction
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have childFixed := assignmentInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 fixedAllocated catalog validated canonical _ assignmentResult
        injection success with resultEq
        rw [← resultEq]
        exact childFixed.of_substitution_eq rfl
  case case61 =>
    intros context item initial fuel target operator value itemEq
      assignmentInduction
    unfold InferForItemFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
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
        have assignmentProperties := assignmentInduction ready wellFormed bound live fixed catalog validated
          canonical (assignment, inferredValue, assignmentState)
          assignmentResult
        exact assignmentProperties
  case case2 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelFixedness
    intro ready _ bound live fixed catalog _ _ expectedBelow expectedSafe result success
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
    have literalFixed : FixesProtected protectedVars literalState := by
      apply fixed.of_substitution_eq
      change allocated.inference.substitution = initial.inference.substitution
      rw [allocatedEq]
      rfl
    exact recordExpressionWithExpected_fixes_protected literalFixed typeSafe
      (fun type member => initialTransport _ (expectedSafe _ member)) recordSuccess
  case case4 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelFixedness
    intro ready _ bound live fixed catalog _ _ expectedBelow expectedSafe result success
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
    have literalFixed : FixesProtected protectedVars literalState := by
      apply fixed.of_substitution_eq
      change allocated.inference.substitution = initial.inference.substitution
      rw [allocatedEq]
      rfl
    exact recordExpressionWithExpected_fixes_protected literalFixed typeSafe
      (fun type member => initialTransport _ (expectedSafe _ member)) recordSuccess
  case case8 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone isBoolean
    unfold InferExprFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
    exact recordExpressionWithExpected_fixes_protected fixedAllocated
      (safe_closed _ _ (Ty.variablesBelow_constructor 0 _)) expectedSafeAtAllocated success
  case case18 =>
    intros context expression expected initial fuel id allocated allocationEq
      marker sourceType expressionEq
    unfold InferExprFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have expectedAtAllocated : ∀ expectedType ∈ expected,
        expectedType.VariablesBelow allocated.inference.next := by
      intro expectedType member
      exact (expectedBelow expectedType member).weaken
        allocationProperties.1.next_le
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        exact recordExpressionWithExpected_fixes_protected fixedAllocated
          ((safe_proxy_iff _ _ _).mpr (safe_closed _ _ (resolveSourceType_success_variablesBelow sourceTypeResult 0)))
          (fun type member => allocationPrivacy.1 _ (expectedSafe type member)) success
  case case49 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq statementEq loopNonzero
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
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
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
    exact fixedAllocated.of_substitution_eq rfl
  case case51 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq statementEq loopNonzero
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
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
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
    exact fixedAllocated.of_substitution_eq rfl
  case case36 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq statementEq
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have returnAtAllocated :=
      returnBelow.weaken allocationProperties.1.next_le
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have unifiedFixed := unify_fixes_protected fixedAllocated unitSafe
          (allocationPrivacy.1 _ returnSafe) unifyResult
        injection success with resultEq
        rw [← resultEq]
        exact unifiedFixed.of_substitution_eq rfl
  case case10 =>
    intros context expression expected initial fuel id allocated allocationEq
      inner expressionEq innerInduction
    unfold InferExprFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have innerPrivacy := inferExprFuel_private protectedVars fuel context inner expected allocated allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          catalog validated canonical expectedAtAllocated expectedSafeAtAllocated (inferred, innerState) innerResult
        have childFixed := innerInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          fixedAllocated catalog validated canonical expectedAtAllocated expectedSafeAtAllocated (inferred, innerState) innerResult
        have innerProperties := inferExprFuel_inferenceProperties allocationProperties.2
          validated canonical expectedAtAllocated innerResult
        have prefixProgress := allocationProperties.1.trans innerProperties.1
        have beforeFit := allocationPrivacy.1.trans innerPrivacy.1
        exact recordExpressionWithExpected_fixes_protected childFixed innerPrivacy.2.1
          (fun type member => beforeFit _ (expectedSafe _ member)) success
  case case11 =>
    intros context expression expected initial fuel id allocated allocationEq
      elements expressionEq elementsInduction
    unfold InferExprFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have elementsPrivacy := inferExprsFuel_private protectedVars fuel context elements.elements allocated allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          catalog validated canonical (inferredElements, elementsState) elementsResult
        have childFixed := elementsInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          fixedAllocated catalog validated canonical (inferredElements, elementsState) elementsResult
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
        exact recordExpressionWithExpected_fixes_protected childFixed tupleSafe
          (fun type member => beforeFit _ (expectedSafe _ member)) success
  case case30 =>
    intros context expectedReturn initial fuel statement rest statementInduction tailInduction
    unfold InferStatementsFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    unfold inferStatementsFuel at success
    cases headResult : inferStatementFuel fuel context statement expectedReturn initial with
    | error error => simp [headResult, bind, Except.bind] at success
    | ok head =>
      simp only [headResult, bind, Except.bind] at success
      have headFixed := statementInduction ready wellFormed bound live fixed catalog validated canonical
        returnBelow returnSafe head headResult
      cases rest with
      | nil =>
        injection success with resultEq
        rw [← resultEq]
        exact headFixed
      | cons next remaining =>
        cases tailResult : inferStatementsFuel fuel context (next :: remaining) expectedReturn head.state with
        | error error => simp [tailResult] at success
        | ok tail =>
          simp only [tailResult] at success
          injection success with resultEq
          rw [← resultEq]
          have headProperties := inferStatementFuel_inferenceProperties ready validated canonical returnBelow headResult
          have headPrivacy := inferStatementFuel_private protectedVars fuel context statement expectedReturn initial
            ready wellFormed bound live catalog validated canonical returnBelow returnSafe head headResult
          exact tailInduction head headProperties.2.1
            ((inferStatementFuel_direct_progress headResult).wellFormed wellFormed)
            (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) headProperties.1.next_le)
            headPrivacy.2.2.1 headFixed catalog validated canonical
            (returnBelow.weaken headProperties.1.next_le) (headPrivacy.1 _ returnSafe) tail tailResult
  case case62 =>
    intros context item initial fuel target operator itemEq placeInduction
    unfold InferForItemFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases placeResult : inferPlaceFuel fuel context target initial with
    | error error =>
        simp [placeResult] at success
    | ok placePair =>
        rcases placePair with ⟨place, placeState⟩
        simp only [placeResult] at success
        have placeProperties := inferPlaceFuel_private protectedVars fuel context target initial ready wellFormed bound live catalog validated canonical
          (place, placeState) placeResult
        have placeFixed := placeInduction ready wellFormed bound live fixed catalog validated canonical
          (place, placeState) placeResult
        cases unifyResult : Detail.unify placeState place.type .word with
        | error error =>
            simp [unifyResult] at success
        | ok unifiedState =>
            simp only [unifyResult, pure, Pure.pure, Except.pure] at success
            injection success with resultEq
            rw [← resultEq]
            have wordSafe : Safe protectedVars placeState .word := safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
            exact unify_fixes_protected placeFixed placeProperties.2.1 wordSafe unifyResult
  case case42 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq target operator statementEq placeInduction
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have placePrivacy := inferPlaceFuel_private protectedVars fuel context target allocated allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical (inferredTarget, placeState) placeResult
        have placeFixed := placeInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 fixedAllocated catalog validated canonical (inferredTarget, placeState) placeResult
        cases unifyResult : Detail.unify placeState inferredTarget.type .word with
        | error error =>
            simp [unifyResult] at success
        | ok unifiedState =>
            simp only [unifyResult, pure, Pure.pure, Except.pure] at success
            have wordSafe : Safe protectedVars placeState .word := safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
            have unifiedFixed := unify_fixes_protected placeFixed placePrivacy.2.1 wordSafe unifyResult
            injection success with resultEq
            rw [← resultEq]
            exact unifiedFixed.of_substitution_eq rfl
  case case70 =>
    intros fuel context target operator value initial placeIH valueIH
    unfold InferAssignedValueFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
    unfold inferAssignedValueFuel at success
    cases placeRun : inferPlaceFuel fuel context target initial with
    | error error => simp [placeRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨place, placeState⟩
      simp only [placeRun, bind, Except.bind] at success
      have placeProperties := inferPlaceFuel_inferenceProperties ready validated canonical placeRun
      have placePrivacy := inferPlaceFuel_private protectedVars fuel context target initial ready wellFormed bound live catalog validated canonical _ placeRun
      have placeFixed := placeIH ready wellFormed bound live fixed catalog validated canonical _ placeRun
      have placeWF := (inferPlaceFuel_direct_progress placeRun).wellFormed wellFormed
      have finishValue (fitted : State)
          (fitProgress : placeState.InferenceProgress fitted)
          (fitReady : fitted.InferenceReady) (fitWF : fitted.RequirementsWellFormed)
          (fitPrivacy : SafeTransport protectedVars placeState fitted)
          (fitLive : LiveBindersSafe protectedVars fitted)
          (fitFixed : FixesProtected protectedVars fitted)
          (fitRows : fitted.requirements = placeState.requirements)
          (expected : Ty) (expectedBelow : expected.VariablesBelow fitted.inference.next)
          (expectedSafe : Safe protectedVars fitted expected)
          (ih : InferExprFuelFixedness protectedVars fuel context value (some expected) fitted)
          (accepted : (do
            let (inferredValue, finalState) ← inferExprFuel fuel context value (some expected) fitted
            pure (({ target := { place with type := finalState.resolve place.type } } : AssignmentResolution), inferredValue, finalState)) = .ok result) :
          FixesProtected protectedVars result.2.2 := by
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
          have valueFixed := ih fitReady fitWF
            (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) (placeProperties.1.trans fitProgress).next_le)
            fitLive fitFixed catalog validated canonical expectedBelow' (by
              intro type member
              simp only [Option.mem_def] at member
              injection member with same
              subst type
              exact expectedSafe) _ valueRun
          exact valueFixed
      have finishNonEqual
          (ih : ∀ fitted, InferExprFuelFixedness protectedVars fuel context value (some .word) fitted)
          (accepted : (do
            let fitted ← Detail.unify placeState place.type .word
            let (inferredValue, finalState) ← inferExprFuel fuel context value (some .word) fitted
            pure (({ target := { place with type := finalState.resolve place.type } } : AssignmentResolution), inferredValue, finalState)) = .ok result) :
          FixesProtected protectedVars result.2.2 := by
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
            (placePrivacy.2.2.1.unify placePrivacy.2.1 wordSafe fittedRun)
            (unify_fixes_protected placeFixed placePrivacy.2.1 wordSafe fittedRun) (Detail.unify_requirements_eq fittedRun)
            .word (Ty.variablesBelow_constructor _ _) (fittedPrivacy _ wordSafe) (ih fitted) accepted
      cases operator with
      | equal =>
        simp only [pure, Pure.pure, Except.pure] at success
        exact finishValue placeState (.refl placeProperties.2.1.solved) placeProperties.2.1 placeWF
          (.refl _ _) placePrivacy.2.2.1 placeFixed rfl (placeState.resolve place.type)
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
  case case39 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq condition thenBody elseBody statementEq
      conditionInduction thenInduction elseInduction
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have conditionPrivacy := inferExprFuel_private protectedVars fuel context condition (some .bool) allocated allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 catalog validated canonical
          (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
          (by intro type member; cases Option.mem_def.mp member; exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _)) _ conditionResult
        have conditionFixed := conditionInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 fixedAllocated catalog validated canonical
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
            have thenPrivacy := inferStatementsFuel_private protectedVars fuel context thenBody.value expectedReturn conditionState conditionProperties.2.1 conditionWF
              (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughCondition.next_le)
              conditionPrivacy.2.2.1 catalog validated canonical
              (returnBelow.weaken throughCondition.next_le) (toCondition _ returnSafe) _ thenResultEq
            have thenFixed := thenInduction conditionState conditionProperties.2.1 conditionWF
              (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughCondition.next_le)
              conditionPrivacy.2.2.1 conditionFixed catalog validated canonical
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
                exact thenFixed.of_substitution_eq rfl
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
                    have elseFixed := elseInduction conditionState thenResult elseBody restoredThen.2
                      (State.restoreLexicalScope_preserves_requirementsWellFormed _ _ thenWF)
                      (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) (throughCondition.trans restoredThen.1).next_le)
                      restoredLive (thenFixed.of_substitution_eq rfl) catalog validated canonical
                      (returnBelow.weaken (throughCondition.trans restoredThen.1).next_le)
                      (toRestored _ returnSafe) _ elseResultEq
                    injection success with resultEq
                    rw [← resultEq]
                    exact elseFixed.of_substitution_eq rfl
  case case46 =>
    intros context statement expectedReturn initial fuel id allocated
      allocationEq condition body statementEq conditionInduction bodyInduction
    unfold InferStatementFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical returnBelow returnSafe result success
    have allocationProperties :=
      allocateStatementId_eq_inferenceProperties ready allocationEq
    let loopContext := { context with loopDepth := context.loopDepth + 1 }
    have loopValidated :
        ProgramSignatureFormationValidated loopContext.signatures := by
      simpa only [loopContext] using validated
    have allocationPrivacy := allocateStatementId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
      have conditionPrivacy := inferExprFuel_private protectedVars fuel context condition (some .bool) allocated allocationProperties.2 wfAllocated boundAllocated
        allocationPrivacy.2.1 catalog validated canonical
        (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
        (by intro type member; cases Option.mem_def.mp member; exact safe_closed _ _ (Ty.variablesBelow_constructor 0 _))
        _ conditionResult
      have conditionFixed := conditionInduction allocationProperties.2 wfAllocated boundAllocated
        allocationPrivacy.2.1 fixedAllocated catalog validated canonical
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
        have bodyFixed := bodyInduction conditionState conditionProperties.2.1
          ((inferExprFuel_direct_progress conditionResult).wellFormed wfAllocated)
          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughCondition.next_le)
          conditionPrivacy.2.2.1 conditionFixed catalog validated canonical
          (returnBelow.weaken throughCondition.next_le)
          (conditionPrivacy.1 _ (allocationPrivacy.1 _ returnSafe)) _ bodyResult
        injection success with resultEq
        rw [← resultEq]
        exact bodyFixed.of_substitution_eq rfl
  case case9 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone notBool
    unfold InferExprFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties := allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
                exact recordExpressionWithExpected_fixes_protected fixedAllocated
                  (safe_closed _ _ (builtinFunction_type_closed function)) expectedSafeAtAllocated success
        | cons signature rest =>
            cases rest with
            | nil =>
                have catalogMember :
                    signature ∈ context.signatures.functions :=
                  functionsNamed_success_subset_catalog functionsResult
                    (by simp)
                exact declaration_reference_fixes_protected catalog catalogMember allocationProperties.2
                  boundAllocated expectedSafeAtAllocated fixedAllocated success
            | cons second tail => simp at success
  case case15 =>
    intro context expression expected initial fuel id allocated allocation keyword parameters returnType body form bodyIH
    exact inferExprFuel_lambda_fixes_protected form bodyIH

  case case23 =>
    intros fuel context source id instantiation arguments expected initial
      arityEq argumentsInduction
    unfold InferConstructorApplicationFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical payloadTypesBelow payloadSafe resultTypeBelow resultSafe
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
            have argumentsPrivacy := inferConstructorArgumentsFuel_private protectedVars fuel context arguments instantiation.payloadTypes initial ready wellFormed bound live catalog validated canonical
              payloadTypesBelow payloadSafe _ argumentsResult
            have argumentsFixed := argumentsInduction initial ready wellFormed bound live fixed catalog validated canonical
              payloadTypesBelow payloadSafe _ argumentsResult
            have resultAtArguments :=
              argumentsProperties.1.resolve_variablesBelow resultTypeBelow
            exact recordExpressionWithExpected_fixes_protected argumentsFixed
              (safe_resolved argumentsProperties.2.1 (argumentsPrivacy.1 _ resultSafe)) (by simp) success
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
            have fitFixed := unify_fixes_protected fixed resultSafe (expectedSafe expectedType (by simp)) fittedResult
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
                have argumentsPrivacy := inferConstructorArgumentsFuel_private protectedVars fuel context arguments instantiation.payloadTypes fittedState fitProperties.2
                  (unify_preserves_requirementsWellFormed fittedResult wellFormed)
                  (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) fitProperties.1.next_le)
                  fitLive catalog validated canonical payloadAtFitted
                  (fun type member => fitTransport _ (payloadSafe type member)) _ argumentsResult
                have argumentsFixed := argumentsInduction fittedState fitProperties.2
                  (unify_preserves_requirementsWellFormed fittedResult wellFormed)
                  (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) fitProperties.1.next_le)
                  fitLive fitFixed catalog validated canonical payloadAtFitted
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
                exact recordExpressionWithExpected_fixes_protected argumentsFixed
                  (safe_resolved argumentsProperties.2.1 (toArguments _ resultSafe))
                  (fun type member => toArguments _ (expectedSafe type member)) success
  case case19 =>
    intros context expression expected initial fuel id allocated allocationEq
      base brackets index expressionEq baseInduction indexInduction
    unfold InferExprFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have basePrivacy := inferExprFuel_private protectedVars fuel context base none allocated allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1 catalog validated canonical (by simp) (by simp) _ baseResult
        have baseFixed := baseInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1 fixedAllocated catalog validated canonical (by simp) (by simp) _ baseResult
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
            have unifiedFixed := unify_fixes_protected (baseFixed.of_substitution_eq (after := valueAllocation.2) rfl)
              baseSafe mappingSafe unifyResult
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
                have keyPrivacy := inferExprFuel_private protectedVars fuel context index (some (unifiedState.resolve baseState.fresh.1)) unifiedState unifiedReady unifiedWF
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
                have keyFixed := indexInduction baseState.fresh.1 unifiedState unifiedReady unifiedWF
                  (fun metavariable member => Nat.lt_of_lt_of_le (baseBound metavariable member)
                    (keyProperties.1.trans (valueProperties.1.trans unifyProgress)).next_le)
                  unifiedLive unifiedFixed catalog validated canonical
                  (by
                    intro type member
                    cases Option.mem_def.mp member
                    exact resolvedKeyBelow)
                  (by
                    intro type member
                    cases Option.mem_def.mp member
                    exact keySafeAtUnified) _ indexResult
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
                exact recordExpressionWithExpected_fixes_protected keyFixed finalValueSafe
                  (fun type member => toIndex _ (expectedSafe type member)) success
  case case68 =>
    intros context target initial fuel base brackets key targetEq
      baseInduction keyInduction
    unfold InferPlaceFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical result success
    unfold inferPlaceFuel at success
    simp only [targetEq, bind, Except.bind] at success
    cases baseResult : inferPlaceFuel fuel context base initial with
    | error error =>
        simp [baseResult] at success
    | ok basePair =>
        rcases basePair with ⟨basePlace, baseState⟩
        simp only [baseResult] at success
        have baseProperties := inferPlaceFuel_inferenceProperties ready validated canonical baseResult
        have basePrivacy := inferPlaceFuel_private protectedVars fuel context base initial ready wellFormed bound live catalog validated canonical _ baseResult
        have baseFixed := baseInduction ready wellFormed bound live fixed catalog validated canonical _ baseResult
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
            have unifiedFixed := unify_fixes_protected (baseFixed.of_substitution_eq (after := valueAllocation.2) rfl)
              baseSafe mappingSafe unifyResult
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
                have keyFixed := keyInduction baseState.fresh.1 unifiedState unifiedReady unifiedWF
                  (fun metavariable member => Nat.lt_of_lt_of_le (baseBound metavariable member)
                    (keyProperties.1.trans (valueProperties.1.trans unifyProgress)).next_le)
                  unifiedLive unifiedFixed catalog validated canonical
                  (by
                    intro type member
                    cases Option.mem_def.mp member
                    exact resolvedKeyBelow)
                  (by
                    intro type member
                    cases Option.mem_def.mp member
                    exact keySafeAtUnified) _ keyResult
                exact keyFixed
  case case12 =>
    intros context expression expected initial fuel id allocated allocationEq
      operator operand expressionEq operandInduction
    unfold InferExprFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have operandPrivacy := inferExprFuel_private protectedVars fuel context operand none allocated allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          catalog validated canonical (by simp) (by simp) (inferredOperand, operandState) operandResult
        have operandFixed := operandInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1 fixedAllocated
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
            FixesProtected protectedVars result.2 := by
          have inferredPrivacy := inferUnaryOperator_private catalog operandProperties.2.1 operandProperties.2.2 expectedAtOperand
            operandPrivacy.2.1 expectedSafeAtOperand operandPrivacy.2.2.1 inferenceSuccess
          have inferredFixed := inferUnaryOperator_fixes_protected operandProperties.2.1
            operandPrivacy.2.1 expectedSafeAtOperand operandFixed inferenceSuccess
          exact recordExpressionWithExpected_fixes_protected inferredFixed inferredPrivacy.2.1
            (fun type member => inferredPrivacy.1 _ (expectedSafeAtOperand _ member)) recordSuccess
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
                        have selectedFixed := selectFunctionCandidateFrom_fixes_protected catalog
                          (functionsNamed_success_subset_catalog functionsResult) operandProperties.2.1
                          (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) prefixProgress.next_le)
                          (by intro argument member; have same := List.mem_singleton.mp member; subst argument; exact operandProperties.2.2)
                          (by intro argument member; have same := List.mem_singleton.mp member; subst argument; exact operandPrivacy.2.1)
                          expectedSafeAtOperand operandPrivacy.2.2.1 operandFixed selectionResult
                        rw [← resultEq]
                        exact recordSelectedCall_fixes_protected expression callee name [inferredOperand] attempt selectedFixed

  case case13 =>
    intros context expression expected initial fuel id allocated allocationEq
      left operator right expressionEq leftInduction rightInduction
    unfold InferExprFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have leftPrivacy := inferExprFuel_private protectedVars fuel context left none allocated allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1
          catalog validated canonical (by simp) (by simp) (inferredLeft, leftState) leftResult
        have leftFixed := leftInduction allocationProperties.2 wfAllocated boundAllocated allocationPrivacy.2.1 fixedAllocated
          catalog validated canonical (by simp) (by simp) (inferredLeft, leftState) leftResult
        have leftProperties := inferExprFuel_inferenceProperties allocationProperties.2 validated canonical (by simp) leftResult
        cases rightResult : inferExprFuel fuel context right none leftState with
        | error error =>
            simp [rightResult] at success
        | ok rightPair =>
            rcases rightPair with ⟨inferredRight, rightState⟩
            simp only [rightResult] at success
            have rightPrivacy := inferExprFuel_private protectedVars fuel context right none leftState leftProperties.2.1
              ((inferExprFuel_direct_progress leftResult).wellFormed wfAllocated)
              (fun metavariable member => Nat.lt_of_lt_of_le (boundAllocated metavariable member) leftProperties.1.next_le)
              leftPrivacy.2.2.1 catalog validated canonical (by simp) (by simp) (inferredRight, rightState) rightResult
            have rightFixed := rightInduction leftState leftProperties.2.1
              ((inferExprFuel_direct_progress leftResult).wellFormed wfAllocated)
              (fun metavariable member => Nat.lt_of_lt_of_le (boundAllocated metavariable member) leftProperties.1.next_le)
              leftPrivacy.2.2.1 leftFixed catalog validated canonical (by simp) (by simp) (inferredRight, rightState) rightResult
            have rightProperties := inferExprFuel_inferenceProperties leftProperties.2.1 validated canonical (by simp) rightResult
            have beforeRight := allocationPrivacy.1.trans (leftPrivacy.1.trans rightPrivacy.1)
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
                FixesProtected protectedVars result.2 := by
              have inferredPrivacy := inferBinaryOperator_private catalog rightProperties.2.1 leftAtRight rightProperties.2.2
                expectedAtRight leftSafeAtRight rightPrivacy.2.1 expectedSafeAtRight rightPrivacy.2.2.1 inferenceSuccess
              have inferredFixed := inferBinaryOperator_fixes_protected rightProperties.2.1 leftAtRight rightProperties.2.2
                leftSafeAtRight rightPrivacy.2.1 expectedSafeAtRight rightFixed inferenceSuccess
              exact recordExpressionWithExpected_fixes_protected inferredFixed inferredPrivacy.2.1
                (fun type member => inferredPrivacy.1 _ (expectedSafeAtRight _ member)) recordSuccess
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
                            have selectedFixed := selectFunctionCandidateFrom_fixes_protected catalog
                              (functionsNamed_success_subset_catalog functionsResult) rightProperties.2.1
                              (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) prefixProgress.next_le)
                              argumentsBelow argumentsSafe (by
                                intro type member
                                cases Option.mem_def.mp member
                                exact safe_closed _ _ (Ty.variablesBelow_constructor _ _))
                              rightPrivacy.2.2.1 rightFixed selectionResult
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
                                have fittedFixed := withExpected_fixes_protected selectedFixed
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
                                rw [← resultEq]
                                exact recordSelectedCallResult_fixes_protected expression callee name
                                  [inferredLeft, inferredRight] attempt fitted.expression fitted.coercions fitted.state fittedFixed


  case case16 =>
    intro context expression expected initial fuel id allocated allocationEq callee arguments expressionEq constructorIH argumentsIH calleeIH
    apply inferExprFuel_call_fixes_protected expressionEq
    · intro instantiation state
      simpa only [allocationEq] using constructorIH instantiation state
    · simpa only [allocationEq] using argumentsIH
    · exact calleeIH
  case case17 =>
    intro context expression expected initial fuel id allocated allocationEq dot name arguments expressionEq constructorIH
    apply inferExprFuel_dotConstructor_fixes_protected expressionEq
    intro dataType constructor typeArguments
    simpa only [allocationEq] using constructorIH dataType constructor typeArguments
  case case20 =>
    intro context expression expected initial fuel id allocated allocationEq base dot name expressionEq constructorIH
    apply inferExprFuel_fieldConstructor_fixes_protected expressionEq
    intro instantiation state
    simpa only [allocationEq] using constructorIH instantiation state
  case case45 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq headerSpan initializer condition post body form initializerIH conditionIH bodyIH postIH
    apply inferStatementFuel_for_fixes_protected form
    · simpa only [allocationEq] using initializerIH
    · exact conditionIH
    · exact bodyIH
    · exact postIH
  case case76 =>
    intro context scrutineeType expectedReturn outerScope initial fuel arm rest bodyIH tailIH
    exact inferMatchCasesFuel_cons_fixes_protected bodyIH tailIH
  case case14 =>
    intros context expression expected initial fuel id allocated allocationEq
      condition question thenBranch colon elseBranch expressionEq
      conditionInduction thenInduction elseInduction
    unfold InferExprFuelFixedness
    intro ready wellFormed bound live fixed catalog validated canonical expectedBelow expectedSafe result success
    have allocationProperties :=
      allocateExpressionId_eq_inferenceProperties ready allocationEq
    have allocationPrivacy := allocateExpressionId_privacy live allocationEq
    have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocationEq).symm
    have fixedAllocated : FixesProtected protectedVars allocated := by
      apply fixed.of_substitution_eq
      rw [allocatedEq]
      rfl
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
        have conditionPrivacy := inferExprFuel_private protectedVars fuel context condition (some .bool) allocated allocationProperties.2 wfAllocated boundAllocated
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
        have conditionFixed := conditionInduction allocationProperties.2 wfAllocated boundAllocated
          allocationPrivacy.2.1 fixedAllocated catalog validated canonical (by
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
            have thenPrivacy := inferExprFuel_private protectedVars fuel context thenBranch expected conditionState conditionProperties.2.1
              ((inferExprFuel_direct_progress conditionResult).wellFormed wfAllocated)
              (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughCondition.next_le)
              conditionPrivacy.2.2.1 catalog validated canonical expectedAtCondition
              (fun type member => toCondition _ (expectedSafe type member))
              (inferredThen, thenState) thenResult
            have thenFixed := thenInduction conditionState conditionProperties.2.1
              ((inferExprFuel_direct_progress conditionResult).wellFormed wfAllocated)
              (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughCondition.next_le)
              conditionPrivacy.2.2.1 conditionFixed catalog validated canonical expectedAtCondition
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
                have elsePrivacy := inferExprFuel_private protectedVars fuel context elseBranch expected thenState thenProperties.2.1
                  ((inferExprFuel_direct_progress thenResult).wellFormed
                    ((inferExprFuel_direct_progress conditionResult).wellFormed wfAllocated))
                  (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughThen.next_le)
                  thenPrivacy.2.2.1 catalog validated canonical expectedAtThen
                  (fun type member => toThen _ (expectedSafe type member))
                  (inferredElse, elseState) elseResult
                have elseFixed := elseInduction thenState thenProperties.2.1
                  ((inferExprFuel_direct_progress thenResult).wellFormed
                    ((inferExprFuel_direct_progress conditionResult).wellFormed wfAllocated))
                  (fun metavariable member => Nat.lt_of_lt_of_le (bound metavariable member) throughThen.next_le)
                  thenPrivacy.2.2.1 thenFixed catalog validated canonical expectedAtThen
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
                    have unifiedFixed := unify_fixes_protected elseFixed thenSafe elsePrivacy.2.1 unifyResult
                    exact recordExpressionWithExpected_fixes_protected unifiedFixed
                      (safe_resolved unifiedReady (unifyPrivacy _ thenSafe))
                      (fun type member => toUnified _ (expectedSafe type member)) success

  case case43 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq scrutinees arms form
    dsimp only
    intro source single casesIH bodyIH sourceIH
    apply inferStatementFuel_match_single_fixes_protected form single casesIH bodyIH
    simpa only [allocationEq] using sourceIH
  case case44 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq scrutinees arms form
    dsimp only
    intro notSingleton casesIH bodyIH sourcesIH
    apply inferStatementFuel_match_many_fixes_protected form notSingleton casesIH bodyIH
    simpa only [allocationEq] using sourcesIH

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferExprFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context expression expected state,
      InferExprFuelFixedness protectedVars fuel context expression expected state :=
  (inferFuel_fixedness_internal protectedVars).1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferConstructorApplicationFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelFixedness protectedVars fuel context source id instantiation arguments expected state :=
  (inferFuel_fixedness_internal protectedVars).2.1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferConstructorArgumentsFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context sources expected state,
      InferConstructorArgumentsFuelFixedness protectedVars fuel context sources expected state :=
  (inferFuel_fixedness_internal protectedVars).2.2.1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferStatementsFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context statements expectedReturn state,
      InferStatementsFuelFixedness protectedVars fuel context statements expectedReturn state :=
  (inferFuel_fixedness_internal protectedVars).2.2.2.1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferStatementFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context statement expectedReturn state,
      InferStatementFuelFixedness protectedVars fuel context statement expectedReturn state :=
  (inferFuel_fixedness_internal protectedVars).2.2.2.2.1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferForItemsFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context items state,
      InferForItemsFuelFixedness protectedVars fuel context items state :=
  (inferFuel_fixedness_internal protectedVars).2.2.2.2.2.1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferForItemFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context item state,
      InferForItemFuelFixedness protectedVars fuel context item state :=
  (inferFuel_fixedness_internal protectedVars).2.2.2.2.2.2.1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferPlaceFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context target state,
      InferPlaceFuelFixedness protectedVars fuel context target state :=
  (inferFuel_fixedness_internal protectedVars).2.2.2.2.2.2.2.1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferAssignedValueFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context target operator value state,
      InferAssignedValueFuelFixedness protectedVars fuel context target operator value state :=
  (inferFuel_fixedness_internal protectedVars).2.2.2.2.2.2.2.2.1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferExprsFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context expressions state,
      InferExprsFuelFixedness protectedVars fuel context expressions state :=
  (inferFuel_fixedness_internal protectedVars).2.2.2.2.2.2.2.2.2.1

/-- Initially fixed protected variables remain fixed through the actual inference call. -/
theorem inferMatchCasesFuel_fixes_protected (protectedVars : List TypeVarId) :
    ∀ fuel context scrutineeType expectedReturn outerScope cases state,
      InferMatchCasesFuelFixedness protectedVars fuel context scrutineeType expectedReturn outerScope cases state :=
  (inferFuel_fixedness_internal protectedVars).2.2.2.2.2.2.2.2.2.2

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
