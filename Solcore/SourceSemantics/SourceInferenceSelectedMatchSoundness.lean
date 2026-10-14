import Solcore.SourceSemantics.SourceInferenceSelectedMatchCases
import Solcore.SourceSemantics.SourceInferenceSelectedMatchScrutinee
import Solcore.SourceSemantics.SourceInferenceSelectedMatchScrutineeScope
import Solcore.SourceSemantics.SourceInferenceSelectedPatternEvidence

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualMatchWithoutDefault
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {finalized : Frontend.SourceInference.Result} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context}
    {evidenceState : Frontend.SourceInference.State}

    {roots : List NodeId}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed target.signatures)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (below : initial.LocalBindersBelowNextLocal)
    (initialInvariant : RecursiveStatementInvariant wholeContext expectedReturn finalized initial target)
    (actual : ActualContext wholeContext finalized frames target)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (outerExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (semanticOwner : target.currentDeclaration = some
      ((result.state.toTypedSource roots).applySubstitution finalized.substitution).owner)
    (evidence : IntegerPatternEvidenceAt
      ((result.state.toTypedSource roots).applySubstitution finalized.substitution) target finalized.substitution
      evidenceState (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource target
      (.statement result.id))
    (closed : OccurrenceGraphClosed finalized.typedSource)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResult : RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (inferenceSignaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters = wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (canonical : SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (returnAdmissible : TypeAdmissible target (finalized.substitution.apply expectedReturn))
    (integerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (integerLiteralsSubset :
      result.state.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (bodyIH : ∀ childFuel, childFuel < fuel+1 → ActualInferStatementsFuelRootedSoundness childFuel)
    (exprIH : ∀ childFuel, childFuel < fuel+1 → ActualInferExprFuelRetainedSoundness childFuel) :
    ∃ facts,
      ActiveLocalContextInvariant result.state finalized.substitution target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution finalized.substitution) {
          returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated finalized.substitution target :=
    initialInvariant.active.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have retained :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [allocatedEq] at retained
    exact retained
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← allocatedEq]
    exact returnBelow
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have retained :=
      Frontend.SourceInference.State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [allocatedEq] at retained
    exact retained
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      scrutineeSuccess, hiddenAllocation, casesSuccess,
      guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq defaultEq
      allocationEq success roots
  have casesPresent : arms.value.cases ≠ [] := by
    intro emptyArms
    have checkedNil : checked.cases = [] := by
      have lengthEq := Detail.inferMatchCasesFuel_success_cases_length
        casesSuccess
      rw [emptyArms] at lengthEq
      simpa using lengthEq
    have wildcardFalse : checked.hasWildcard = false := by
      cases wildcardEq : checked.hasWildcard with
      | false => rfl
      | true =>
          obtain ⟨arm, armMember, _⟩ :=
            Detail.inferMatchCasesFuel_success_hasWildcard_member
              casesSuccess wildcardEq
          simp [checkedNil] at armMember
    have nominalFalse : Detail.exhaustsNominalConstructors
        inferenceContext checked.state scrutinee.type checked.cases = false := by
      simp [checkedNil, Detail.exhaustsNominalConstructors]
    simp [wildcardFalse, nominalFalse] at guardPassed
  have scrutineeProperties := inferMatchScrutineesFuel_inferenceProperties
    allocatedReady signatureFormation functionsCanonical scrutineeSuccess
  have scrutineeInvariant :
      ActiveLocalContextInvariant scrutineeState finalized.substitution target :=
    allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have scrutineeLocalBelow :
      scrutineeState.LocalBindersBelowNextLocal :=
    inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal
      allocatedBelow scrutineeSuccess
  have hiddenInvariant : ActiveLocalContextInvariant hiddenState finalized.substitution target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have hiddenReady : hiddenState.InferenceReady := by
    have retained :=
      Frontend.SourceInference.State.InferenceReady.allocateHiddenLocal
        scrutineeProperties.2.1
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have hiddenScrutineeBelow :
      scrutinee.type.VariablesBelow hiddenState.inference.next := by
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact scrutineeProperties.2.2
  have hiddenReturnBelow :
      expectedReturn.VariablesBelow hiddenState.inference.next := by
    have atScrutinee :=
      allocatedReturnBelow.weaken scrutineeProperties.1.next_le
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact atScrutinee
  have hiddenBelow : hiddenState.LocalBindersBelowNextLocal := by
    have retained :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_localBindersBelowNextLocal
        scrutineeState scrutineeLocalBelow
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have checkedInvariant : ActiveLocalContextInvariant checked.state finalized.substitution
      target := hiddenInvariant.inferMatchCasesFuel casesSuccess
  have checkedIntegerPatternsSubset :
      checked.state.integerPatterns ⊆ result.state.integerPatterns := by
    rw [resultEq]
    intro origin member
    exact member
  have checkedIntegerLiteralsSubset :
      checked.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro origin member
    simpa [Frontend.SourceInference.State.recordNode] using member
  have checkedRequirementsSubset :
      checked.state.requirements ⊆ result.state.requirements := by
    rw [resultEq]
    exact Frontend.SourceInference.State.recordNode_requirements_subset
      checked.state _
  have checkedRequirementsOccur : ∀ matchCase,
      matchCase ∈ checked.cases →
      ∀ requirement, requirement ∈ matchCase.pattern.requirements →
        PrimaryRequirementOccursAt
          ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
          (.statement result.id) requirement := by
    intro matchCase caseMember requirement requirementMember
    rw [FlexibleSubstitution.primaryRequirementOccursAt_applySubstitution]
    exact contains.matchCasePatternRequirementOccursAt rfl caseMember
      requirementMember
  have checkedCasesCovered : ∀ matchCase,
      matchCase ∈ checked.cases →
      ∀ child, child ∈ matchCase.body →
        TemplateScopeCovered finalized.typedSource target (.statement child) := by
    intro matchCase caseMember child childMember
    have reference : (.statement child : NodeId) ∈
        (StatementForm.matchWith {
          scrutinee := scrutinee.id
          hiddenScrutinee
          cases := checked.cases
          defaultBody := none
          requirements := checked.cases.flatMap fun arm =>
            arm.pattern.requirements
        }).references := by
      simp only [StatementForm.references, MatchResolution.references]
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨matchCase, caseMember,
        by simpa [TypedMatchCase.references] using
          (List.mem_map.mpr ⟨child, childMember, rfl⟩ :
            NodeId.statement child ∈ matchCase.body.map NodeId.statement)⟩
    exact rooted_statement_child_covered contains reference resultExtension parentCovered closed
      (fun _ member => member)
  have allocatedNodesBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have scrutineeNodesBelow :
      scrutineeState.NodesBelowNextOccurrence :=
    inferMatchScrutineesFuel_success_nodesBelow scrutineeSuccess
      allocatedNodesBelow
  have hiddenNodesBelow : hiddenState.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence
        scrutineeState scrutineeNodesBelow
    have eq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    simpa [eq] using bound
  have checkedToResult : TypingSourceExtends
      ((checked.state.toTypedSource roots).applySubstitution finalized.substitution)
      ((result.state.toTypedSource roots).applySubstitution finalized.substitution) := by
    have raw : TypingSourceExtends
        (checked.state.toTypedSource roots)
        (result.state.toTypedSource roots) := by
      rw [resultEq]
      refine ⟨rfl, ?_⟩
      simp only [Frontend.SourceInference.State.toTypedSource,
        Frontend.SourceInference.State.recordNode]
      exact List.prefix_append _ _
    exact raw.applySubstitution finalized.substitution
  have checkedExtension : finalized.substitution.SemanticallyExtends
      checked.state.inference.substitution := by
    simpa [resultEq, State.recordNode] using outerExtension
  have checkedOwner : checked.state.owner = hiddenState.owner :=
    Detail.inferMatchCasesFuel_preserves_owner casesSuccess
  have hiddenProperties := Detail.inferMatchCasesFuel_inferenceProperties
    hiddenReady signatureFormation functionsCanonical hiddenScrutineeBelow hiddenReturnBelow rfl casesSuccess
  have hiddenExtension := checkedExtension.trans hiddenProperties.1.substitution_extends
  have hiddenBinders : hiddenState.localBinders = initial.localBinders := by
    have alloc := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    have scr := congrArg LexicalScope.binders (inferMatchScrutineesFuel_success_lexicalScope_eq scrutineeSuccess)
    have hidden : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← hidden]
    exact scr.trans alloc
  have hiddenOperational : ActualStateInvariant hiddenState (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, tracked⟩ := operational.ledger
    have allocatedTracked : RecursiveLedgerInvariant allocated pending := by simpa [allocationEq] using tracked.allocateStatementId
    have scrutineeTracked := inferMatchScrutineesFuel_ledger scrutineeSuccess
      (actualLedgerFamily fuel).expression (actualLedgerFamily fuel).expressions allocatedTracked
    have hiddenTracked : RecursiveLedgerInvariant hiddenState pending := by simpa [hiddenAllocation] using scrutineeTracked.allocateHiddenLocal
    exact ⟨⟨pending, hiddenTracked⟩, operational.origins.congr_localBinders hiddenBinders,
      monomorphicBinders_bound (fun binder member => operational.monomorphicBinders binder (hiddenBinders ▸ member)),
      operational.sourceMonomorphic⟩
  have hiddenRecursive : RecursiveStatementInvariant wholeContext expectedReturn finalized hiddenState target := {
    initialInvariant with
    active := hiddenInvariant
    ready := hiddenReady
    returnBelow := hiddenReturnBelow
    bindersBelow := hiddenBelow
    nodesBelow := hiddenNodesBelow
    schemeIsolation := monomorphicBinders_isolation hiddenOperational.monomorphicBinders
    substitutionExtension := hiddenExtension }
  have checkedRaw : TypingSourceExtends (checked.state.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    exact ⟨rfl, List.prefix_append _ _⟩
  have scrutineeToHidden : TypingSourceExtends (scrutineeState.toTypedSource roots)
      (hiddenState.toTypedSource roots) := by
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same]
    exact ⟨rfl, List.prefix_rfl⟩
  have scrutineeRaw := scrutineeToHidden.trans
    ((inferMatchCasesFuel_success_typingSourceExtends casesSuccess hiddenNodesBelow roots).trans checkedRaw)
  have scrutineeExtension : finalized.substitution.SemanticallyExtends scrutineeState.inference.substitution := by
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same] at hiddenExtension
    exact hiddenExtension
  have scrutineeReference : (.expression scrutinee.id : NodeId) ∈
      (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases,
        defaultBody := none,
        requirements := checked.cases.flatMap fun arm => arm.pattern.requirements }).references := by
    simp [StatementForm.references, MatchResolution.references]
  have scrutineePatterns : scrutineeState.integerPatterns ⊆ checked.state.integerPatterns := by
    have rows := Detail.inferMatchCasesFuel_integerPatterns_subset casesSuccess
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same] at rows
    exact rows
  have scrutineeLiterals : scrutineeState.integerLiterals ⊆ checked.state.integerLiterals := by
    have rows := Detail.inferMatchCasesFuel_integerLiterals_subset casesSuccess
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same] at rows
    exact rows
  have scrutineeRequirements : scrutineeState.requirements ⊆ checked.state.requirements := by
    have rows := Detail.inferMatchCasesFuel_requirements_subset casesSuccess
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same] at rows
    exact rows
  have scrutineeTyping := actualInferMatchScrutineesFuelRootedSoundness exprIH scrutineeSuccess
    resources interfaces scrutineeExtension inferenceSignaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical (by simpa only [← signatures_eq] using catalog) canonical
    (RecursiveExpressionInvariant.ofStatement (initialInvariant.allocateStatementId allocationEq))
    actual (operational.allocateStatementId allocationEq)
    (SubtreePreserved.ofTypingSourceExtends (scrutineeRaw.applySubstitution finalized.substitution))
    ((rawResult.child (directChild_statement_reference contains scrutineeReference)).monoBefore scrutineeRaw)
    (scrutineePatterns.trans (checkedIntegerPatternsSubset.trans integerPatternsSubset))
    (scrutineeLiterals.trans (checkedIntegerLiteralsSubset.trans integerLiteralsSubset))
    (scrutineeRequirements.trans (checkedRequirementsSubset.trans requirementsSubset))
    (by
      apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
        parentCovered closed (resultExtension.containsStatement contains)
      · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
      · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references,
          MatchResolution.applySubstitution, MatchResolution.references])
    (parentActualCovered.preserved_statement_reference contains resultExtension scrutineeReference)
  have caseReference : ∀ matchCase ∈ checked.cases, ∀ child ∈ matchCase.body,
      (.statement child : NodeId) ∈ (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases, defaultBody := none,
        requirements := checked.cases.flatMap fun arm => arm.pattern.requirements }).references := by
    intro matchCase caseMember child childMember
    simp only [StatementForm.references, MatchResolution.references]
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨matchCase, caseMember, by
      simpa [TypedMatchCase.references] using
        (List.mem_map.mpr ⟨child, childMember, rfl⟩ : NodeId.statement child ∈ matchCase.body.map NodeId.statement)⟩
  obtain ⟨caseFacts, casesTyping, allReturnEq⟩ :=
    actualMatchCases_sound resources interfaces inferenceSignaturesEq ownerEq parametersEq assumptionsEq
      signatureFormation functionsCanonical (by simpa only [← signatures_eq] using catalog) canonical
      hiddenRecursive actual hiddenOperational returnAdmissible evidence hiddenScrutineeBelow
      (by
        simpa [resultEq, State.toTypedSource, State.restoreLexicalScope, State.recordNode,
          TypedSource.applySubstitution] using checkedOwner)
      semanticOwner scrutineeTyping.type_admissible rfl checkedExtension checkedToResult
      (checkedIntegerPatternsSubset.trans integerPatternsSubset)
      (checkedIntegerLiteralsSubset.trans integerLiteralsSubset)
      (checkedRequirementsSubset.trans requirementsSubset) checkedRequirementsOccur checkedCasesCovered
      (fun arm armMember child childMember => parentActualCovered.preserved_statement_reference
        contains resultExtension (caseReference arm armMember child childMember))
      (fun arm armMember child childMember => (rawResult.child
        (directChild_statement_reference contains (caseReference arm armMember child childMember))).monoBefore checkedRaw)
      (fun child bound => bodyIH child (Nat.lt_trans bound (Nat.lt_succ_self fuel))) casesSuccess
  have exhaustive :=
    matchExhaustiveWithoutDefault_of_guard catalog signatures_eq casesSuccess
      casesTyping scrutineeTyping.type_admissible checkedExtension guardPassed
  have checkedCasesPresent : checked.cases ≠ [] := by
    intro checkedCasesEq
    have lengthEq := Detail.inferMatchCasesFuel_success_cases_length
      casesSuccess
    rw [checkedCasesEq] at lengthEq
    apply casesPresent
    simpa using lengthEq.symm
  have caseFactsPresent : caseFacts ≠ [] :=
    matchCasesHaveType_facts_ne_nil_of_cases_ne_nil casesTyping (by
      simpa using checkedCasesPresent)
  obtain ⟨summary, merged⟩ :=
    mergeBodyControls_withoutDefault_eq_some_of_ne_nil caseFacts
      caseFactsPresent
  subst result
  refine ⟨{
      type := if allBodiesSawReturn caseFacts then
        finalized.substitution.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts
      sawReturn := allBodiesSawReturn caseFacts
      control := summary.eraseValue
    }, checkedInvariant.recordNode _, ?_, ?_⟩
  · exact matchWithoutDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping exhaustive allReturnEq merged
      checkedExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithoutDefault
      allReturnEq checkedExtension id _


theorem actualMatchWithDefault
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {finalized : Frontend.SourceInference.Result} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context}
    {evidenceState : Frontend.SourceInference.State}

    {roots : List NodeId}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed target.signatures)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (below : initial.LocalBindersBelowNextLocal)
    (initialInvariant : RecursiveStatementInvariant wholeContext expectedReturn finalized initial target)
    (actual : ActualContext wholeContext finalized frames target)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (outerExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (semanticOwner : target.currentDeclaration = some
      ((result.state.toTypedSource roots).applySubstitution finalized.substitution).owner)
    (evidence : IntegerPatternEvidenceAt
      ((result.state.toTypedSource roots).applySubstitution finalized.substitution) target finalized.substitution
      evidenceState (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource target
      (.statement result.id))
    (closed : OccurrenceGraphClosed finalized.typedSource)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResult : RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (inferenceSignaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters = wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (canonical : SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (returnAdmissible : TypeAdmissible target (finalized.substitution.apply expectedReturn))
    (integerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (integerLiteralsSubset :
      result.state.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (exprIH : ∀ childFuel, childFuel < fuel+1 → ActualInferExprFuelRetainedSoundness childFuel)
    (bodyIH : ∀ childFuel, childFuel < fuel+1 → ActualInferStatementsFuelRootedSoundness childFuel) :
    ∃ facts,
      ActiveLocalContextInvariant result.state finalized.substitution target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution finalized.substitution) {
          returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated finalized.substitution target :=
    initialInvariant.active.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have retained :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [allocatedEq] at retained
    exact retained
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← allocatedEq]
    exact returnBelow
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have retained :=
      Frontend.SourceInference.State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    have allocatedEq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [allocatedEq] at retained
    exact retained
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      defaultResult, scrutineeSuccess, hiddenAllocation, casesSuccess,
      defaultSuccess, _guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithDefault_facts statementEq defaultEq
      allocationEq success roots
  have scrutineeProperties := inferMatchScrutineesFuel_inferenceProperties
    allocatedReady signatureFormation functionsCanonical scrutineeSuccess
  have scrutineeInvariant :
      ActiveLocalContextInvariant scrutineeState finalized.substitution target :=
    allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have scrutineeLocalBelow :
      scrutineeState.LocalBindersBelowNextLocal :=
    inferMatchScrutineesFuel_preserves_localBindersBelowNextLocal
      allocatedBelow scrutineeSuccess
  have hiddenInvariant : ActiveLocalContextInvariant hiddenState finalized.substitution target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have hiddenReady : hiddenState.InferenceReady := by
    have retained :=
      Frontend.SourceInference.State.InferenceReady.allocateHiddenLocal
        scrutineeProperties.2.1
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have hiddenScrutineeBelow :
      scrutinee.type.VariablesBelow hiddenState.inference.next := by
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact scrutineeProperties.2.2
  have hiddenReturnBelow :
      expectedReturn.VariablesBelow hiddenState.inference.next := by
    have atScrutinee :=
      allocatedReturnBelow.weaken scrutineeProperties.1.next_le
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [← hiddenEq]
    exact atScrutinee
  have hiddenBelow : hiddenState.LocalBindersBelowNextLocal := by
    have retained :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_localBindersBelowNextLocal
        scrutineeState scrutineeLocalBelow
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    rw [hiddenEq] at retained
    exact retained
  have checkedProperties := Detail.inferMatchCasesFuel_inferenceProperties
    hiddenReady signatureFormation functionsCanonical hiddenScrutineeBelow
      hiddenReturnBelow rfl casesSuccess
  have checkedInvariant : ActiveLocalContextInvariant checked.state finalized.substitution
      target := hiddenInvariant.inferMatchCasesFuel casesSuccess
  have checkedReturnBelow :=
    hiddenReturnBelow.weaken checkedProperties.1.next_le
  have defaultProperties := Detail.inferStatementsFuel_inferenceProperties
    checkedProperties.2.1 signatureFormation functionsCanonical
      checkedReturnBelow defaultSuccess
  have checkedIntegerPatternsSubset :
      checked.state.integerPatterns ⊆ result.state.integerPatterns := by
    rw [resultEq]
    have throughDefault : checked.state.integerPatterns ⊆
        defaultResult.state.integerPatterns :=
      Detail.inferStatementsFuel_integerPatterns_subset defaultSuccess
    have throughRestore : defaultResult.state.integerPatterns ⊆
        (defaultResult.state.restoreLexicalScope
          hiddenState.lexicalScope).integerPatterns := by
      intro origin member
      exact member
    apply List.Subset.trans throughDefault
    apply List.Subset.trans throughRestore
    intro origin member
    exact member
  have checkedIntegerLiteralsSubset :
      checked.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    have throughDefault : checked.state.integerLiterals ⊆
        defaultResult.state.integerLiterals :=
      Detail.inferStatementsFuel_integerLiterals_subset defaultSuccess
    have throughRestore : defaultResult.state.integerLiterals ⊆
        (defaultResult.state.restoreLexicalScope
          hiddenState.lexicalScope).integerLiterals := by
      intro origin member
      exact member
    apply List.Subset.trans throughDefault
    apply List.Subset.trans throughRestore
    intro origin member
    simpa [Frontend.SourceInference.State.recordNode] using member
  have checkedRequirementsSubset :
      checked.state.requirements ⊆ result.state.requirements := by
    rw [resultEq]
    exact List.Subset.trans
      (Detail.inferStatementsFuel_requirements_subset defaultSuccess)
      (List.Subset.trans
        (Frontend.SourceInference.State.restoreLexicalScope_requirements_subset
          defaultResult.state hiddenState.lexicalScope)
        (Frontend.SourceInference.State.recordNode_requirements_subset
          (defaultResult.state.restoreLexicalScope hiddenState.lexicalScope)
          _))
  have checkedRequirementsOccur : ∀ matchCase,
      matchCase ∈ checked.cases →
      ∀ requirement, requirement ∈ matchCase.pattern.requirements →
        PrimaryRequirementOccursAt
          ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
          (.statement result.id) requirement := by
    intro matchCase caseMember requirement requirementMember
    rw [FlexibleSubstitution.primaryRequirementOccursAt_applySubstitution]
    exact contains.matchCasePatternRequirementOccursAt rfl caseMember
      requirementMember
  have checkedCasesCovered : ∀ matchCase,
      matchCase ∈ checked.cases →
      ∀ child, child ∈ matchCase.body →
        TemplateScopeCovered finalized.typedSource target (.statement child) := by
    intro matchCase caseMember child childMember
    have reference : (.statement child : NodeId) ∈
        (StatementForm.matchWith {
          scrutinee := scrutinee.id
          hiddenScrutinee
          cases := checked.cases
          defaultBody := some defaultResult.statements
          requirements := checked.cases.flatMap fun arm =>
            arm.pattern.requirements
        }).references := by
      simp only [StatementForm.references, MatchResolution.references]
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨matchCase, caseMember,
        by simpa [TypedMatchCase.references] using
          (List.mem_map.mpr ⟨child, childMember, rfl⟩ :
            NodeId.statement child ∈ matchCase.body.map NodeId.statement)⟩
    exact rooted_statement_child_covered contains reference resultExtension parentCovered closed
      (fun _ member => member)
  have defaultCovered : ∀ child, child ∈ defaultResult.statements →
      TemplateScopeCovered finalized.typedSource target (.statement child) := by
    intro child childMember
    have reference : (.statement child : NodeId) ∈
        (StatementForm.matchWith {
          scrutinee := scrutinee.id
          hiddenScrutinee
          cases := checked.cases
          defaultBody := some defaultResult.statements
          requirements := checked.cases.flatMap fun arm =>
            arm.pattern.requirements
        }).references := by
      simp only [StatementForm.references, MatchResolution.references]
      apply List.mem_append_right
      simpa using
        (List.mem_map.mpr ⟨child, childMember, rfl⟩ :
          NodeId.statement child ∈
            defaultResult.statements.map NodeId.statement)
    exact rooted_statement_child_covered contains reference resultExtension parentCovered closed
      (fun _ member => member)
  have allocatedNodesBelow : allocated.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateStatementId_preserves_nodesBelowNextOccurrence
        initial initialBelow
    have eq : initial.allocateStatementId.2 = allocated :=
      congrArg Prod.snd allocationEq
    simpa [eq] using bound
  have scrutineeNodesBelow :
      scrutineeState.NodesBelowNextOccurrence :=
    inferMatchScrutineesFuel_success_nodesBelow scrutineeSuccess
      allocatedNodesBelow
  have hiddenNodesBelow : hiddenState.NodesBelowNextOccurrence := by
    have bound :=
      Frontend.SourceInference.State.allocateHiddenLocal_preserves_nodesBelowNextOccurrence
        scrutineeState scrutineeNodesBelow
    have eq : scrutineeState.allocateHiddenLocal.2 = hiddenState :=
      congrArg Prod.snd hiddenAllocation
    simpa [eq] using bound
  have checkedNodesBelow : checked.state.NodesBelowNextOccurrence :=
    (Detail.inferMatchCasesFuel_occurrenceBoundExtends casesSuccess
      ).nodesBelowNextOccurrence hiddenNodesBelow
  have defaultToResultRaw : TypingSourceExtends
      (defaultResult.state.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    exact ⟨rfl, List.prefix_append _ _⟩
  have defaultToResult : TypingSourceExtends
      ((defaultResult.state.toTypedSource roots).applySubstitution finalized.substitution)
      ((result.state.toTypedSource roots).applySubstitution finalized.substitution) :=
    defaultToResultRaw.applySubstitution finalized.substitution
  have checkedToDefault : TypingSourceExtends
      (checked.state.toTypedSource roots)
      (defaultResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends defaultSuccess
      checkedNodesBelow roots
  have checkedToResult : TypingSourceExtends
      ((checked.state.toTypedSource roots).applySubstitution finalized.substitution)
      ((result.state.toTypedSource roots).applySubstitution finalized.substitution) :=
    (TypingSourceExtends.trans checkedToDefault defaultToResultRaw
      ).applySubstitution finalized.substitution
  have defaultIntegerPatternsSubset :
      defaultResult.state.integerPatterns ⊆
        evidenceState.integerPatterns := by
    apply List.Subset.trans ?_ integerPatternsSubset
    rw [resultEq]
    intro x member
    exact member
  have defaultIntegerLiteralsSubset :
      defaultResult.state.integerLiterals ⊆
        evidenceState.integerLiterals := by
    apply List.Subset.trans ?_ integerLiteralsSubset
    rw [resultEq]
    intro origin member
    simpa [Frontend.SourceInference.State.restoreLexicalScope,
      Frontend.SourceInference.State.recordNode] using member
  have defaultRequirementsSubset :
      defaultResult.state.requirements ⊆
        evidenceState.requirements := by
    apply List.Subset.trans ?_ requirementsSubset
    rw [resultEq]
    intro x member
    exact member
  have defaultExtension : finalized.substitution.SemanticallyExtends
      defaultResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using outerExtension
  have checkedExtension : finalized.substitution.SemanticallyExtends
      checked.state.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans defaultExtension
      defaultProperties.1.substitution_extends
  have checkedOwner : checked.state.owner = hiddenState.owner :=
    Detail.inferMatchCasesFuel_preserves_owner casesSuccess
  have defaultOwner : defaultResult.state.owner = checked.state.owner :=
    Detail.inferStatementsFuel_preserves_owner defaultSuccess
  have hiddenProperties := Detail.inferMatchCasesFuel_inferenceProperties
    hiddenReady signatureFormation functionsCanonical hiddenScrutineeBelow hiddenReturnBelow rfl casesSuccess
  have hiddenExtension := checkedExtension.trans hiddenProperties.1.substitution_extends
  have hiddenBinders : hiddenState.localBinders = initial.localBinders := by
    have alloc := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    have scr := congrArg LexicalScope.binders (inferMatchScrutineesFuel_success_lexicalScope_eq scrutineeSuccess)
    have hidden : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← hidden]
    exact scr.trans alloc
  have hiddenOperational : ActualStateInvariant hiddenState (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, tracked⟩ := operational.ledger
    have allocatedTracked : RecursiveLedgerInvariant allocated pending := by simpa [allocationEq] using tracked.allocateStatementId
    have scrutineeTracked := inferMatchScrutineesFuel_ledger scrutineeSuccess
      (actualLedgerFamily fuel).expression (actualLedgerFamily fuel).expressions allocatedTracked
    have hiddenTracked : RecursiveLedgerInvariant hiddenState pending := by simpa [hiddenAllocation] using scrutineeTracked.allocateHiddenLocal
    exact ⟨⟨pending, hiddenTracked⟩, operational.origins.congr_localBinders hiddenBinders,
      monomorphicBinders_bound (fun binder member => operational.monomorphicBinders binder (hiddenBinders ▸ member)),
      operational.sourceMonomorphic⟩
  have hiddenRecursive : RecursiveStatementInvariant wholeContext expectedReturn finalized hiddenState target := {
    initialInvariant with
    active := hiddenInvariant
    ready := hiddenReady
    returnBelow := hiddenReturnBelow
    bindersBelow := hiddenBelow
    nodesBelow := hiddenNodesBelow
    schemeIsolation := monomorphicBinders_isolation hiddenOperational.monomorphicBinders
    substitutionExtension := hiddenExtension }
  have checkedRaw : TypingSourceExtends (checked.state.toTypedSource roots)
      (result.state.toTypedSource roots) := checkedToDefault.trans defaultToResultRaw
  have scrutineeToHidden : TypingSourceExtends (scrutineeState.toTypedSource roots)
      (hiddenState.toTypedSource roots) := by
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same]
    exact ⟨rfl, List.prefix_rfl⟩
  have scrutineeRaw := scrutineeToHidden.trans
    ((inferMatchCasesFuel_success_typingSourceExtends casesSuccess hiddenNodesBelow roots).trans checkedRaw)
  have scrutineeExtension : finalized.substitution.SemanticallyExtends scrutineeState.inference.substitution := by
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same] at hiddenExtension
    exact hiddenExtension
  have scrutineeReference : (.expression scrutinee.id : NodeId) ∈
      (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases,
        defaultBody := some defaultResult.statements,
        requirements := checked.cases.flatMap fun arm => arm.pattern.requirements }).references := by
    simp [StatementForm.references, MatchResolution.references]
  have scrutineePatterns : scrutineeState.integerPatterns ⊆ checked.state.integerPatterns := by
    have rows := Detail.inferMatchCasesFuel_integerPatterns_subset casesSuccess
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same] at rows
    exact rows
  have scrutineeLiterals : scrutineeState.integerLiterals ⊆ checked.state.integerLiterals := by
    have rows := Detail.inferMatchCasesFuel_integerLiterals_subset casesSuccess
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same] at rows
    exact rows
  have scrutineeRequirements : scrutineeState.requirements ⊆ checked.state.requirements := by
    have rows := Detail.inferMatchCasesFuel_requirements_subset casesSuccess
    have same : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    rw [← same] at rows
    exact rows
  have scrutineeTyping := actualInferMatchScrutineesFuelRootedSoundness exprIH scrutineeSuccess
    resources interfaces scrutineeExtension inferenceSignaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical (by simpa only [← signatures_eq] using catalog) canonical
    (RecursiveExpressionInvariant.ofStatement (initialInvariant.allocateStatementId allocationEq))
    actual (operational.allocateStatementId allocationEq)
    (SubtreePreserved.ofTypingSourceExtends (scrutineeRaw.applySubstitution finalized.substitution))
    ((rawResult.child (directChild_statement_reference contains scrutineeReference)).monoBefore scrutineeRaw)
    (scrutineePatterns.trans (checkedIntegerPatternsSubset.trans integerPatternsSubset))
    (scrutineeLiterals.trans (checkedIntegerLiteralsSubset.trans integerLiteralsSubset))
    (scrutineeRequirements.trans (checkedRequirementsSubset.trans requirementsSubset))
    (by
      apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
        parentCovered closed (resultExtension.containsStatement contains)
      · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
      · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references,
          MatchResolution.applySubstitution, MatchResolution.references])
    (parentActualCovered.preserved_statement_reference contains resultExtension scrutineeReference)
  have caseReference : ∀ matchCase ∈ checked.cases, ∀ child ∈ matchCase.body,
      (.statement child : NodeId) ∈ (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases,
        defaultBody := some defaultResult.statements,
        requirements := checked.cases.flatMap fun arm => arm.pattern.requirements }).references := by
    intro matchCase caseMember child childMember
    simp only [StatementForm.references, MatchResolution.references]
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨matchCase, caseMember, by
      simpa [TypedMatchCase.references] using
        (List.mem_map.mpr ⟨child, childMember, rfl⟩ : NodeId.statement child ∈ matchCase.body.map NodeId.statement)⟩
  obtain ⟨caseFacts, casesTyping, caseReturnEq⟩ :=
    actualMatchCases_sound resources interfaces inferenceSignaturesEq ownerEq parametersEq assumptionsEq
      signatureFormation functionsCanonical (by simpa only [← signatures_eq] using catalog) canonical
      hiddenRecursive actual hiddenOperational returnAdmissible evidence hiddenScrutineeBelow
      (by
        simpa [resultEq, State.toTypedSource, State.restoreLexicalScope, State.recordNode,
          TypedSource.applySubstitution] using defaultOwner.trans checkedOwner)
      semanticOwner scrutineeTyping.type_admissible rfl checkedExtension checkedToResult
      (checkedIntegerPatternsSubset.trans integerPatternsSubset)
      (checkedIntegerLiteralsSubset.trans integerLiteralsSubset)
      (checkedRequirementsSubset.trans requirementsSubset) checkedRequirementsOccur checkedCasesCovered
      (fun arm armMember child childMember => parentActualCovered.preserved_statement_reference
        contains resultExtension (caseReference arm armMember child childMember))
      (fun arm armMember child childMember => (rawResult.child
        (directChild_statement_reference contains (caseReference arm armMember child childMember))).monoBefore checkedRaw)
      (fun child bound => bodyIH child (Nat.lt_trans bound (Nat.lt_succ_self fuel))) casesSuccess
  have checkedBinders : checked.state.localBinders = hiddenState.localBinders :=
    congrArg LexicalScope.binders (Detail.inferMatchCasesFuel_success_lexicalScope_eq rfl casesSuccess)
  have checkedOperational : ActualStateInvariant checked.state (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := hiddenOperational.ledger
    exact ⟨⟨pending, (actualLedgerFamily fuel).statements.matchCases casesSuccess ledger⟩,
      hiddenOperational.origins.congr_localBinders checkedBinders,
      activeQuantifiersBelowNext_transport hiddenOperational.quantifiersBelow checkedBinders checkedProperties.1.next_le,
      operational.sourceMonomorphic⟩
  have checkedRecursive : RecursiveStatementInvariant wholeContext expectedReturn finalized checked.state target := {
    hiddenRecursive with
    active := checkedInvariant
    ready := checkedProperties.2.1
    returnBelow := checkedReturnBelow
    bindersBelow := State.LocalBindersBelowNextLocal.transport checkedBinders
      (Detail.inferMatchCasesFuel_nextLocal_le casesSuccess) hiddenBelow
    nodesBelow := checkedNodesBelow
    schemeIsolation := monomorphicBinders_isolation checkedOperational.monomorphicBinders
    substitutionExtension := checkedExtension }
  have defaultReference : ∀ child ∈ defaultResult.statements, (.statement child : NodeId) ∈
      (StatementForm.matchWith {
        scrutinee := scrutinee.id, hiddenScrutinee, cases := checked.cases,
        defaultBody := some defaultResult.statements,
        requirements := checked.cases.flatMap fun arm => arm.pattern.requirements }).references := by
    intro child member
    simp only [StatementForm.references, MatchResolution.references]
    apply List.mem_append_right
    simpa using (List.mem_map.mpr ⟨child, member, rfl⟩ : NodeId.statement child ∈ defaultResult.statements.map NodeId.statement)
  obtain ⟨defaultFinal, defaultFacts, _defaultInvariant, _defaultActual, _defaultOperational,
      defaultTyping, defaultAgreement⟩ :=
    bodyIH fuel (Nat.lt_succ_self fuel) defaultSuccess resources interfaces inferenceSignaturesEq
      ownerEq parametersEq assumptionsEq signatureFormation functionsCanonical
      (by simpa only [← signatures_eq] using catalog) canonical checkedRecursive actual checkedOperational
      returnAdmissible defaultExtension
      (fun _ _ => SubtreePreserved.ofTypingSourceExtends defaultToResult)
      (fun child member => (rawResult.child (directChild_statement_reference contains
        (defaultReference child member))).monoBefore defaultToResultRaw)
      defaultIntegerPatternsSubset defaultIntegerLiteralsSubset defaultRequirementsSubset defaultCovered
      (fun child member => parentActualCovered.preserved_statement_reference contains resultExtension
        (defaultReference child member))
  obtain ⟨summary, merged⟩ :=
    mergeBodyControls_withDefault_eq_some caseFacts defaultFacts
  subst result
  refine ⟨{
      type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then
        finalized.substitution.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      control := summary.eraseValue
    }, hiddenInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact matchWithDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping defaultTyping caseReturnEq defaultAgreement
      merged defaultExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithDefault
      caseReturnEq defaultAgreement defaultExtension id _


private theorem matchBinders
    {fuel : Nat} {context : Frontend.SourceInference.Context} {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId} {result : Detail.StatementResult}
    (form : statement.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (accepted : Detail.inferStatementFuel (fuel+1) context statement expectedReturn initial = .ok result) :
    result.state.localBinders = initial.localBinders := by
  cases defaultEq : arms.value.defaultBody with
  | none =>
    obtain ⟨scrutinee, scrutineeState, hidden, hiddenState, checked, scrutineeSuccess,
      hiddenAllocation, casesSuccess, _guard, resultEq, _contains⟩ :=
      inferStatementFuel_success_matchWithoutDefault_facts form defaultEq allocation accepted []
    have checkedScope := Detail.inferMatchCasesFuel_success_lexicalScope_eq rfl casesSuccess
    have scrutineeScope := inferMatchScrutineesFuel_success_lexicalScope_eq scrutineeSuccess
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    have allocatedScope := Detail.allocateStatementId_success_lexicalScope allocation
    have hiddenBinders : hiddenState.localBinders = allocated.localBinders := by
      rw [← hiddenEq]
      exact congrArg LexicalScope.binders scrutineeScope
    have checkedBinders := congrArg LexicalScope.binders checkedScope
    simpa only [resultEq, State.recordNode, State.lexicalScope] using
      checkedBinders.trans (hiddenBinders.trans (congrArg LexicalScope.binders allocatedScope))
  | some defaultBody =>
    obtain ⟨scrutinee, scrutineeState, hidden, hiddenState, checked, defaultResult, scrutineeSuccess,
      hiddenAllocation, _casesSuccess, _defaultSuccess, _guard, resultEq, _contains⟩ :=
      inferStatementFuel_success_matchWithDefault_facts form defaultEq allocation accepted []
    have scrutineeScope := inferMatchScrutineesFuel_success_lexicalScope_eq scrutineeSuccess
    have hiddenEq : scrutineeState.allocateHiddenLocal.2 = hiddenState := congrArg Prod.snd hiddenAllocation
    have allocatedScope := Detail.allocateStatementId_success_lexicalScope allocation
    have hiddenBinders : hiddenState.localBinders = allocated.localBinders := by
      rw [← hiddenEq]
      exact congrArg LexicalScope.binders scrutineeScope
    simpa only [resultEq, State.recordNode, State.restoreLexicalScope, State.lexicalScope] using
      hiddenBinders.trans (congrArg LexicalScope.binders allocatedScope)

theorem actualInferStatementFuelRootedSoundness_match {fuel : Nat}
    (exprIH : ∀ childFuel, childFuel < fuel+1 → ActualInferExprFuelRetainedSoundness childFuel)
    (bodyIH : ∀ childFuel, childFuel < fuel+1 → ActualInferStatementsFuelRootedSoundness childFuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .matchWith scrutinees arms →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement scrutinees arms initial result evidenceState roots finalized
    semanticSource frames semanticContext form accepted resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog canonical invariant actual operational returnAdmissible outerExtension
    _semantic raw patterns literals requirements covered actualCovered
  generalize allocation : initial.allocateStatementId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have finalPreserved := raw.finalized resources
  have semanticSignatures : semanticContext.signatures = inferenceContext.signatures :=
    invariant.signaturesEq.trans signaturesEq.symm
  have semanticOwner : semanticContext.currentDeclaration =
      some ((result.state.toTypedSource roots).applySubstitution finalized.substitution).owner := by
    change semanticContext.currentDeclaration = some (result.state.toTypedSource roots).owner
    rw [← finalPreserved.owner_eq, actual.sourceOwner]
    exact invariant.declarationEq
  have evidence := IntegerPatternEvidenceAt.restrictSubtree finalPreserved
    (resources.integerPatternEvidenceAt invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered)
  have branch : ∃ facts, ActiveLocalContextInvariant result.state finalized.substitution semanticContext ∧
      StatementHasType ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        {returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
        semanticContext result.id semanticContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
    cases defaultEq : arms.value.defaultBody with
    | none =>
      exact actualMatchWithoutDefault form defaultEq allocation accepted formation functions
        (by simpa only [semanticSignatures] using catalog) semanticSignatures invariant.ready invariant.returnBelow
        invariant.bindersBelow invariant actual operational outerExtension invariant.nodesBelow semanticOwner evidence
        covered resources.graph_closed finalPreserved raw actualCovered resources interfaces signaturesEq ownerEq
        parametersEq assumptionsEq canonical returnAdmissible patterns literals requirements bodyIH exprIH
    | some defaultBody =>
      exact actualMatchWithDefault form defaultEq allocation accepted formation functions
        (by simpa only [semanticSignatures] using catalog) semanticSignatures invariant.ready invariant.returnBelow
        invariant.bindersBelow invariant actual operational outerExtension invariant.nodesBelow semanticOwner evidence
        covered resources.graph_closed finalPreserved raw actualCovered resources interfaces signaturesEq ownerEq
        parametersEq assumptionsEq canonical returnAdmissible patterns literals requirements exprIH bodyIH
  have bindersEq := matchBinders form allocation accepted
  have isolation : ActiveSchemeQuantifierIsolation result.state :=
    activeSchemeQuantifierIsolation_transport invariant.schemeIsolation bindersEq
  obtain ⟨facts, active, typed, agreement⟩ := branch
  obtain ⟨finalContext, finalFacts, finalInvariant, finalTyping, finalAgreement⟩ :=
    RecursiveStatementInvariant.close_statement_branch invariant accepted formation functions
      (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow accepted)
      outerExtension isolation ⟨semanticContext, facts, active, typed, agreement⟩
  have properties := Detail.inferStatementFuel_inferenceProperties invariant.ready formation functions invariant.returnBelow accepted
  exact ⟨finalContext, finalFacts, finalInvariant, actual.of_statement finalTyping,
    operational.ofStatementPreservingBinders accepted bindersEq properties.1.next_le, finalTyping, finalAgreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
