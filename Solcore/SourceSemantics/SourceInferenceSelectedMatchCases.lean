import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicLet
import Solcore.SourceSemantics.SourceInferenceSelectedPatternMonomorphism

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem ActualStateInvariant.ofPattern
    {fuel : Nat} {context : Frontend.SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {initial final : State} {inferred : TypedMatchPattern} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected initial = .ok (inferred, final)) :
    ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have mono := PatternMonomorphism.inferMatchPatternFuel_preserves_monomorphicBinders
    accepted invariant.monomorphicBinders
  exact ⟨⟨pending, inferMatchPatternFuel_ledgerPreservation accepted ledger⟩,
    ActiveBinderCaptureOrigins.of_monomorphic mono,
    monomorphicBinders_bound mono, invariant.sourceMonomorphic⟩

theorem actualMatchCases_sound_with_extra
    (extra : SourceSemantics.Context → Detail.BlockResult → Prop)
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {scrutineeType expectedReturn : TypeSystem.Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : Frontend.SourceInference.State}
    {result : Detail.MatchCasesResult}
    {source : TypedSource} {control : ControlContext}
    {outer : TypeSystem.Substitution}
    {semanticContext : SourceSemantics.Context}
    {evidenceState : Frontend.SourceInference.State} {occurrence : NodeId}
    {roots : List NodeId}
    (validated : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (semanticSignaturesEq :
      semanticContext.signatures = inferenceContext.signatures)
    (evidence : IntegerPatternEvidenceAt source semanticContext outer
      evidenceState occurrence)
    (operational : ActualStateInvariant state (evidenceState.toTypedSource roots))
    (ready : state.InferenceReady)
    (scrutineeBelow :
      scrutineeType.VariablesBelow state.inference.next)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (below : state.LocalBindersBelowNextLocal)
    (initialBelow : state.NodesBelowNextOccurrence)
    (owner_eq : source.owner = state.owner)
    (semanticOwner : semanticContext.currentDeclaration = some source.owner)
    (scrutineeAdmissible :
      TypeAdmissible semanticContext (outer.apply scrutineeType))
    (initialInvariant :
      ActiveLocalContextInvariant state outer semanticContext)
    (scopeEq : state.lexicalScope = outerScope)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (resultSourceExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer) source)
    (integerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (requirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (requirementsOccur : ∀ matchCase,
      matchCase ∈ result.cases →
      ∀ requirement, requirement ∈ matchCase.pattern.requirements →
        PrimaryRequirementOccursAt source occurrence requirement)
    (extraHead :
      ∀ {arm : Syntax.MatchCase} {pattern : TypedMatchPattern}
        {bodyResult : Detail.BlockResult} {binders : List TypedBinder}
        {armContext : SourceSemantics.Context},
        ({ span := arm.span, pattern, body := bodyResult.statements } :
          TypedMatchCase) ∈ result.cases →
        BindersExtend source.owner semanticContext binders armContext →
        extra armContext bodyResult)
    (bodySound :
      ∀ {childFuel : Nat} {statements : List Syntax.Statement}
        {childInitial : Frontend.SourceInference.State}
        {childResult : Detail.BlockResult}
        {childContext : SourceSemantics.Context},
        childFuel < fuel →
        ActualStateInvariant childInitial (evidenceState.toTypedSource roots) →
        ActiveLocalContextInvariant childInitial outer childContext →
        Detail.inferStatementsFuel childFuel inferenceContext statements
            expectedReturn childInitial = .ok childResult →
        childInitial.InferenceReady →
        expectedReturn.VariablesBelow childInitial.inference.next →
        childInitial.LocalBindersBelowNextLocal →
        childInitial.NodesBelowNextOccurrence →
        outer.SemanticallyExtends childResult.state.inference.substitution →
        TypingSourceExtends
          (childResult.state.toTypedSource roots)
          (result.state.toTypedSource roots) →
        TypingSourceExtends
          ((childResult.state.toTypedSource roots).applySubstitution outer)
          source →
        childResult.state.integerPatterns ⊆ evidenceState.integerPatterns →
        childResult.state.integerLiterals ⊆ result.state.integerLiterals →
        childResult.state.requirements ⊆ evidenceState.requirements →
        extra childContext childResult →
          ∃ finalContext facts,
            ActiveLocalContextInvariant childResult.state outer finalContext ∧
            StatementsHaveType source control childContext
              childResult.statements finalContext facts ∧
            BlockResultMatchesFactsAfterSubstitution outer childResult facts)
    (success : Detail.inferMatchCasesFuel fuel inferenceContext scrutineeType
      expectedReturn outerScope cases state = .ok result) :
    ∃ caseFacts,
      MatchCasesHaveType source control semanticContext
        (outer.apply scrutineeType)
        (result.cases.map (TypedMatchCase.applySubstitution outer)) caseFacts ∧
      allBodiesSawReturn caseFacts = result.allReturn := by
  induction fuel generalizing outerScope cases state result with
  | zero =>
      simp [Detail.inferMatchCasesFuel] at success
  | succ fuel induction =>
      cases cases with
      | nil =>
          unfold Detail.inferMatchCasesFuel at success
          injection success with resultEq
          subst result
          exact ⟨[], .nil control semanticContext
            (outer.apply scrutineeType), rfl⟩
      | cons arm rest =>
          have traversalSuccess := success
          unfold Detail.inferMatchCasesFuel at success
          simp only [bind, Except.bind] at success
          cases patternSuccess : Detail.inferMatchPatternFuel fuel
              inferenceContext arm.value.pattern scrutineeType state with
          | error error =>
              simp [patternSuccess] at success
          | ok patternPair =>
              rcases patternPair with ⟨pattern, patternState⟩
              simp only [patternSuccess] at success
              cases bodySuccess : Detail.inferStatementsFuel fuel
                  inferenceContext arm.value.body.value expectedReturn
                  patternState with
              | error error =>
                  simp [bodySuccess] at success
              | ok bodyResult =>
                  simp only [bodySuccess] at success
                  let tailInput :=
                    bodyResult.state.restoreLexicalScope outerScope
                  cases tailSuccess : Detail.inferMatchCasesFuel fuel
                      inferenceContext scrutineeType expectedReturn outerScope
                      rest tailInput with
                  | error error =>
                      simp [tailInput, tailSuccess] at success
                  | ok tail =>
                      simp only [tailInput, tailSuccess, pure, Pure.pure,
                        Except.pure] at success
                      injection success with resultEq
                      subst result
                      have patternProperties :=
                        Detail.inferMatchPatternFuel_inferenceProperties ready
                          scrutineeBelow validated patternSuccess
                      have patternNodesBelow :
                          patternState.NodesBelowNextOccurrence :=
                        (Detail.inferMatchPatternFuel_occurrenceBoundExtends
                          patternSuccess).nodesBelowNextOccurrence initialBelow
                      have bodyNodesBelow :
                          bodyResult.state.NodesBelowNextOccurrence :=
                        (Detail.inferStatementsFuel_occurrenceBoundExtends
                          bodySuccess).nodesBelowNextOccurrence
                            patternNodesBelow
                      have tailInputNodesBelow :
                          tailInput.NodesBelowNextOccurrence :=
                        Frontend.SourceInference.State.restoreLexicalScope_preserves_nodesBelowNextOccurrence
                          bodyResult.state outerScope bodyNodesBelow
                      have tailInputSourceExtension : TypingSourceExtends
                          (tailInput.toTypedSource roots)
                          (tail.state.toTypedSource roots) := by
                        constructor
                        · exact Detail.inferMatchCasesFuel_preserves_owner
                            tailSuccess
                        · exact Detail.inferMatchCasesFuel_preserves_nodesPrefix
                            tailSuccess (nodesPrefix := List.prefix_rfl)
                              (baseBelow := tailInputNodesBelow)
                              (cutoffLe := Nat.le_refl _)
                      have bodySourceExtension : TypingSourceExtends
                          ((bodyResult.state.toTypedSource roots).applySubstitution
                            outer) source := by
                        have bodyToTailInput : TypingSourceExtends
                            (bodyResult.state.toTypedSource roots)
                            (tailInput.toTypedSource roots) :=
                          ⟨rfl, List.prefix_rfl⟩
                        exact ((TypingSourceExtends.trans bodyToTailInput
                          tailInputSourceExtension).applySubstitution outer).trans
                            resultSourceExtension
                      have bodyRawResultExtension : TypingSourceExtends
                          (bodyResult.state.toTypedSource roots)
                          (tail.state.toTypedSource roots) := by
                        have bodyToTailInput : TypingSourceExtends
                            (bodyResult.state.toTypedSource roots)
                            (tailInput.toTypedSource roots) :=
                          ⟨rfl, List.prefix_rfl⟩
                        exact TypingSourceExtends.trans bodyToTailInput
                          tailInputSourceExtension
                      have bodyIntegerPatternsSubset :
                          bodyResult.state.integerPatterns ⊆
                            evidenceState.integerPatterns :=
                        List.Subset.trans (by
                          simpa [tailInput,
                            Frontend.SourceInference.State.restoreLexicalScope]
                            using
                              (Detail.inferMatchCasesFuel_integerPatterns_subset
                                tailSuccess)) integerPatternsSubset
                      have bodyIntegerLiteralsSubset :
                          bodyResult.state.integerLiterals ⊆
                            tail.state.integerLiterals := by
                        simpa [tailInput,
                          Frontend.SourceInference.State.restoreLexicalScope]
                          using
                            (Detail.inferMatchCasesFuel_integerLiterals_subset
                              tailSuccess)
                      have bodyRequirementsSubset :
                          bodyResult.state.requirements ⊆
                            evidenceState.requirements :=
                        List.Subset.trans (by
                          simpa [tailInput,
                            Frontend.SourceInference.State.restoreLexicalScope]
                            using
                              (Detail.inferMatchCasesFuel_requirements_subset
                                tailSuccess)) requirementsSubset
                      have returnAtPattern :=
                        returnBelow.weaken patternProperties.1.next_le
                      have bodyProperties :=
                        Detail.inferStatementsFuel_inferenceProperties
                          patternProperties.2.1 validated functionsCanonical
                          returnAtPattern bodySuccess
                      have throughBody :=
                        patternProperties.1.trans bodyProperties.1
                      have restoredProperties :
                          state.InferenceProgress tailInput ∧
                            tailInput.InferenceReady := by
                        unfold tailInput
                        rw [← scopeEq]
                        exact Frontend.SourceInference.State.restoreLexicalScope_inferenceProperties
                          ready throughBody
                      have tailScrutineeBelow :=
                        scrutineeBelow.weaken restoredProperties.1.next_le
                      have tailReturnBelow :=
                        returnBelow.weaken restoredProperties.1.next_le
                      have tailProperties :=
                        Detail.inferMatchCasesFuel_inferenceProperties
                          (outerScope := outerScope) (state := tailInput)
                          (result := tail)
                          restoredProperties.2 validated functionsCanonical
                          tailScrutineeBelow tailReturnBelow (by
                            simp [tailInput]) tailSuccess
                      change outer.SemanticallyExtends
                        tail.state.inference.substitution at outerExtension
                      have outerTailInput : outer.SemanticallyExtends
                          tailInput.inference.substitution :=
                        TypeSystem.Substitution.SemanticallyExtends.trans
                          outerExtension
                          tailProperties.1.substitution_extends
                      have outerBody : outer.SemanticallyExtends
                          bodyResult.state.inference.substitution := by
                        simpa [tailInput,
                          Frontend.SourceInference.State.restoreLexicalScope]
                          using outerTailInput
                      have outerPattern : outer.SemanticallyExtends
                          patternState.inference.substitution :=
                        TypeSystem.Substitution.SemanticallyExtends.trans
                          outerBody bodyProperties.1.substitution_extends
                      have patternMetadata :=
                        Detail.inferMatchCasesFuel_headPatternState_metadata_subset
                          patternSuccess bodySuccess traversalSuccess
                      have patternIntegerPatternsSubset :
                          patternState.integerPatterns ⊆
                            evidenceState.integerPatterns :=
                        List.Subset.trans patternMetadata.1
                          integerPatternsSubset
                      have patternRequirementsSubset :
                          patternState.requirements ⊆
                            evidenceState.requirements :=
                        List.Subset.trans patternMetadata.2
                          requirementsSubset
                      have patternRequirementsOccur : ∀ requirement,
                          requirement ∈ pattern.requirements →
                            PrimaryRequirementOccursAt source occurrence
                              requirement := by
                        intro requirement member
                        exact requirementsOccur {
                          span := arm.span
                          pattern
                          body := bodyResult.statements
                        } (by simp) requirement member
                      obtain ⟨patternCertificate⟩ :=
                        inferMatchPatternFuel_success_sound_at validated
                          catalog semanticSignaturesEq evidence ready
                          scrutineeBelow below owner_eq semanticOwner
                          scrutineeAdmissible initialInvariant outerPattern
                          patternIntegerPatternsSubset
                          patternRequirementsSubset patternRequirementsOccur
                          patternSuccess
                      have patternOperationalState := operational.ofPattern patternSuccess
                      have headExtra : extra patternCertificate.armContext
                          bodyResult :=
                        extraHead (arm := arm) (pattern := pattern)
                          (bodyResult := bodyResult)
                          (binders := patternCertificate.binders)
                          (armContext := patternCertificate.armContext)
                          (by simp) patternCertificate.binders_extend
                      obtain ⟨finalContext, headFacts, _bodyInvariant,
                          headBodyTyping, headBodyAgreement⟩ :=
                        bodySound (Nat.lt_succ_self fuel) patternOperationalState
                          patternCertificate.pattern_invariant bodySuccess
                          patternProperties.2.1 returnAtPattern
                          patternCertificate.pattern_below patternNodesBelow
                          outerBody bodyRawResultExtension bodySourceExtension
                          bodyIntegerPatternsSubset bodyIntegerLiteralsSubset
                          bodyRequirementsSubset headExtra
                      let headCertificate : MatchCaseInferenceCertificate
                          source control semanticContext outer scrutineeType
                          pattern patternState bodyResult := {
                        binders := patternCertificate.binders
                        rootArity := patternCertificate.rootArity
                        armContext := patternCertificate.armContext
                        finalContext
                        facts := headFacts
                        pattern_type := patternCertificate.pattern_type
                        binders_extend := patternCertificate.binders_extend
                        pattern_invariant := patternCertificate.pattern_invariant
                        body_type := headBodyTyping
                        body_matches := headBodyAgreement
                      }
                      obtain ⟨headFacts, headTyping, headAgreement⟩ :=
                        headCertificate.toMatchCaseHasType
                          (arm := arm)
                      have tailInvariant : ActiveLocalContextInvariant
                          tailInput outer semanticContext := by
                        unfold tailInput
                        rw [← scopeEq]
                        exact initialInvariant.restoreLexicalScope
                      have patternNextLocal :
                          state.nextLocal ≤ patternState.nextLocal :=
                        Detail.inferMatchPatternFuel_nextLocal_le patternSuccess
                      have bodyNextLocal :
                          patternState.nextLocal ≤
                            bodyResult.state.nextLocal :=
                        Detail.inferStatementsFuel_nextLocal_le bodySuccess
                      have tailNextLocal :
                          state.nextLocal ≤ tailInput.nextLocal := by
                        simpa [tailInput] using
                          Nat.le_trans patternNextLocal bodyNextLocal
                      have tailBelow : tailInput.LocalBindersBelowNextLocal := by
                        apply Frontend.SourceInference.State.LocalBindersBelowNextLocal.transport
                          (before := state) (after := tailInput)
                        · change outerScope.binders = state.localBinders
                          simpa [Frontend.SourceInference.State.lexicalScope]
                            using congrArg LexicalScope.binders scopeEq.symm
                        · exact tailNextLocal
                        · exact below
                      have patternOwner : patternState.owner = state.owner :=
                        Detail.inferMatchPatternFuel_preserves_owner
                          patternSuccess
                      have bodyOwner :
                          bodyResult.state.owner = patternState.owner :=
                        Detail.inferStatementsFuel_preserves_owner bodySuccess
                      have tailOwner : source.owner = tailInput.owner := by
                        simpa [tailInput,
                          Frontend.SourceInference.State.restoreLexicalScope]
                          using owner_eq.trans
                            (patternOwner.symm.trans bodyOwner.symm)
                      have tailScopeEq : tailInput.lexicalScope = outerScope := by
                        simp [tailInput]
                      have tailRequirementsOccur : ∀ matchCase,
                          matchCase ∈ tail.cases →
                          ∀ requirement,
                            requirement ∈ matchCase.pattern.requirements →
                              PrimaryRequirementOccursAt source occurrence
                                requirement := by
                        intro matchCase caseMember requirement member
                        exact requirementsOccur matchCase (by
                          simp [caseMember]) requirement member
                      have tailOperational : ActualStateInvariant tailInput
                          (evidenceState.toTypedSource roots) := by
                        obtain ⟨pending, ledger⟩ := patternOperationalState.ledger
                        have bindersEq : tailInput.localBinders = state.localBinders := by
                          change outerScope.binders = state.localBinders
                          exact congrArg LexicalScope.binders scopeEq.symm
                        refine ⟨⟨pending, ((actualLedgerFamily fuel).statements.statements
                          bodySuccess ledger).restoreLexicalScope outerScope⟩,
                          operational.origins.congr_localBinders bindersEq,
                          activeQuantifiersBelowNext_transport operational.quantifiersBelow
                            bindersEq restoredProperties.1.next_le,
                          operational.sourceMonomorphic⟩
                      obtain ⟨tailFacts, tailTyping, tailAgreement⟩ :=
                        induction tailOperational restoredProperties.2 tailScrutineeBelow
                          tailReturnBelow tailBelow tailInputNodesBelow
                          tailOwner tailInvariant tailScopeEq outerExtension
                          resultSourceExtension integerPatternsSubset
                          requirementsSubset tailRequirementsOccur
                          (fun {arm} {pattern} {bodyResult} {binders}
                            {armContext} member binderExtension =>
                            extraHead (arm := arm) (pattern := pattern)
                              (bodyResult := bodyResult) (binders := binders)
                              (armContext := armContext)
                              (by simp [member]) binderExtension)
                          (fun childBound childOperational childInvariant childSuccess
                            childReady childReturnBelow childBindersBelow
                            childBelow childSubstitutionExtension
                            childRawExtension childExtension childIntegerSubset
                            childLiteralSubset childRequirementSubset
                            childExtra =>
                            bodySound
                              (Nat.lt_trans childBound (Nat.lt_succ_self fuel))
                              childOperational childInvariant childSuccess childReady
                              childReturnBelow childBindersBelow childBelow
                              childSubstitutionExtension childRawExtension
                              childExtension childIntegerSubset
                                childLiteralSubset childRequirementSubset
                                childExtra)
                          tailSuccess
                      refine ⟨headFacts :: tailFacts, ?_, ?_⟩
                      · simpa only [List.map_cons] using
                          (MatchCasesHaveType.cons headTyping tailTyping)
                      · change (headFacts.sawReturn &&
                            allBodiesSawReturn tailFacts) =
                          (bodyResult.sawReturn && tail.allReturn)
                        rw [headAgreement.sawReturn_eq, tailAgreement]



private theorem binderContextFacts {owner : Resolved.DeclarationId}
    {before after : SourceSemantics.Context} {binders : List TypedBinder}
    (extension : BindersExtend owner before binders after) :
    after.signatures = before.signatures ∧
    after.typeParameters = before.typeParameters ∧
    after.currentDeclaration = before.currentDeclaration ∧
    after.residualTypeVariables = before.residualTypeVariables ∧
    after.solvedRequirements = before.solvedRequirements ∧
    after.assumptions = before.assumptions := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons head tail ih =>
    cases head
    simpa only [SourceSemantics.Context.withLocal] using ih

private theorem admissibleLocal {context : SourceSemantics.Context} {type : Ty}
    (typed : TypeAdmissible context type) (binder : TypedBinder) :
    TypeAdmissible (context.withLocal binder.id binder.scheme binder.schemeRequirements) type :=
  StructuralSubstitution.TypeAdmissible.transportContext (source := context)
    (target := context.withLocal binder.id binder.scheme binder.schemeRequirements) rfl rfl rfl rfl rfl typed

private theorem admissibleBinders {owner : Resolved.DeclarationId}
    {before after : SourceSemantics.Context} {binders : List TypedBinder} {type : Ty}
    (extension : BindersExtend owner before binders after)
    (typed : TypeAdmissible before type) : TypeAdmissible after type := by
  induction extension with
  | nil => exact typed
  | cons head tail ih =>
    apply ih
    cases head
    exact admissibleLocal typed _

theorem actualMatchCases_sound
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn scrutineeType : Ty}
    {state evidenceState : State} {result : Detail.MatchCasesResult}
    {cases : List Syntax.MatchCase} {outerScope : LexicalScope}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context}
    {source : TypedSource} {occurrence : NodeId}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters = wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (formation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functions : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (canonical : SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn finalized state semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant state (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (evidence : IntegerPatternEvidenceAt source semanticContext finalized.substitution evidenceState occurrence)
    (scrutineeBelow : scrutineeType.VariablesBelow state.inference.next)
    (sourceOwner : source.owner = state.owner)
    (semanticOwner : semanticContext.currentDeclaration = some source.owner)
    (scrutineeAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply scrutineeType))
    (scopeEq : state.lexicalScope = outerScope)
    (outerExtension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution finalized.substitution) source)
    (patterns : result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (literals : result.state.integerLiterals ⊆ evidenceState.integerLiterals)
    (requirements : result.state.requirements ⊆ evidenceState.requirements)
    (occurs : ∀ matchCase ∈ result.cases, ∀ requirement ∈ matchCase.pattern.requirements,
      PrimaryRequirementOccursAt source occurrence requirement)
    (covered : ∀ matchCase ∈ result.cases, ∀ child ∈ matchCase.body,
      TemplateScopeCovered finalized.typedSource semanticContext (.statement child))
    (actualCovered : ∀ matchCase ∈ result.cases, ∀ child ∈ matchCase.body,
      ActualContext.Covers finalized frames (.statement child))
    (raw : ∀ matchCase ∈ result.cases, ∀ child ∈ matchCase.body,
      RawSubtreePreserved (result.state.toTypedSource roots)
        (evidenceState.toTypedSource roots) (.statement child))
    (bodyIH : ∀ childFuel, childFuel < fuel → ActualInferStatementsFuelRootedSoundness childFuel)
    (accepted : Detail.inferMatchCasesFuel fuel inferenceContext scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    ∃ facts, MatchCasesHaveType source
      {returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
      semanticContext (finalized.substitution.apply scrutineeType)
      (result.cases.map (TypedMatchCase.applySubstitution finalized.substitution)) facts ∧
      allBodiesSawReturn facts = result.allReturn := by
  have semanticSignatures : semanticContext.signatures = inferenceContext.signatures :=
    invariant.signaturesEq.trans signaturesEq.symm
  apply actualMatchCases_sound_with_extra
    (extra := fun armContext bodyResult => ∃ binders,
      BindersExtend source.owner semanticContext binders armContext ∧
      (∀ child ∈ bodyResult.statements,
        TemplateScopeCovered finalized.typedSource semanticContext (.statement child)) ∧
      (∀ child ∈ bodyResult.statements, ActualContext.Covers finalized frames (.statement child)) ∧
      (∀ child ∈ bodyResult.statements, RawSubtreePreserved (result.state.toTypedSource roots)
        (evidenceState.toTypedSource roots) (.statement child)))
    formation functions (by simpa only [semanticSignatures] using catalog) semanticSignatures
    evidence operational invariant.ready scrutineeBelow invariant.returnBelow invariant.bindersBelow
    invariant.nodesBelow sourceOwner semanticOwner scrutineeAdmissible invariant.active scopeEq
    outerExtension resultExtension patterns requirements occurs ?_ ?_ accepted
  · intro arm pattern bodyResult binders armContext member extension
    exact ⟨binders, extension, covered _ member, actualCovered _ member, raw _ member⟩
  · intro childFuel statements childInitial childResult childContext childBound childOperational
      childActive childSuccess childReady childReturn childBinders childNodes childSubstitution
      childRaw childExtension childPatterns childLiterals childRequirements childExtra
    obtain ⟨binders, extension, childCovered, childActualCovered, childRawCovered⟩ := childExtra
    obtain ⟨sig, params, owner, residual, solved, assumptions⟩ := binderContextFacts extension
    have childInvariant : RecursiveStatementInvariant wholeContext expectedReturn finalized
        childInitial childContext := {
      active := childActive
      ready := childReady
      returnBelow := childReturn
      bindersBelow := childBinders
      nodesBelow := childNodes
      schemeIsolation := monomorphicBinders_isolation childOperational.monomorphicBinders
      substitutionExtension := childSubstitution.trans
        (Detail.inferStatementsFuel_inferenceProperties childReady formation functions childReturn childSuccess).1.substitution_extends
      signaturesEq := sig.trans invariant.signaturesEq
      typeParametersEq := params.trans invariant.typeParametersEq
      declarationEq := owner.trans invariant.declarationEq
      residual := residual.trans invariant.residual
      solvedRequirementsEq := solved.trans invariant.solvedRequirementsEq
      assumptionsMono := by simpa only [assumptions] using invariant.assumptionsMono }
    obtain ⟨finalContext, facts, resultInvariant, _resultActual, _resultOperational, typed, agreement⟩ :=
      bodyIH childFuel childBound childSuccess resources interfaces signaturesEq ownerEq parametersEq
        assumptionsEq formation functions catalog canonical childInvariant (actual.binders extension)
        childOperational (admissibleBinders extension returnAdmissible) childSubstitution
        (fun _ _ => SubtreePreserved.ofTypingSourceExtends childExtension)
        (fun child member => (childRawCovered child member).monoBefore childRaw)
        childPatterns (childLiterals.trans literals) childRequirements
        (by
          intro child member owner scopes
          change owner.requirement.predicate ∈ childContext.assumptions
          rw [assumptions]
          exact childCovered child member owner scopes)
        childActualCovered
    exact ⟨finalContext, facts, resultInvariant.active, typed, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
