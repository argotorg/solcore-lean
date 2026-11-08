import Solcore.SourceSemantics.Internal.Selected.Lets
import Solcore.SourceSemantics.Internal.Selected.PatternMonomorphism
import Solcore.SourceSemantics.Internal.Selected.Children
import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Inference.Soundness
import Solcore.SourceSemantics.Internal.Inference.Subtrees

/-!
# Selected matches

Scrutinee traversal, cases and the match soundness theorem.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedMatchCases
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedMatchScrutinee
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

/-- The actual common match-scrutinee traversal retains a single expression,
or its actual ordered children under the generated ordinary tuple. -/
theorem actualInferMatchScrutineesFuelRootedSoundness {fuel : Nat}
    (recursive : ∀ smaller, smaller < fuel + 1 → ActualInferExprFuelRetainedSoundness smaller) :
∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial resultState evidenceState : State}
    {inferred : InferredExpression} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    inferMatchScrutineesFuel fuel inferenceContext span sources initial =
        .ok (inferred, resultState) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
    finalized.substitution.SemanticallyExtends
      resultState.inference.substitution →
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
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    SubtreePreserved finalized.substitution
      (resultState.toTypedSource roots) semanticSource (.expression inferred.id) →
    RawSubtreePreserved (resultState.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.expression inferred.id) →
    resultState.integerPatterns ⊆ evidenceState.integerPatterns →
    resultState.integerLiterals ⊆ evidenceState.integerLiterals →
    resultState.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id) →
    ActualContext.Covers finalized frames (.expression inferred.id) →
    ExpressionHasType semanticSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type) := by
  intro wholeContext inferenceContext wholeReturn span sources initial resultState evidenceState inferred roots finalized
    semanticSource frames semanticContext success resources interfaces extension signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog canonical invariant actual operational semantic raw patterns literals requirements covered actualCovered
  have finalPreserved : SubtreePreserved finalized.substitution (resultState.toTypedSource roots)
      finalized.typedSource (.expression inferred.id) := by
    rw [resources.source_eq]
    exact raw.substituted finalized.substitution
  have generated {elements : List InferredExpression} {elementsState allocated : State} {tupleId : ExpressionId}
      (elementsSuccess : Detail.inferExprsFuel fuel inferenceContext sources initial = .ok (elements, elementsState))
      (allocation : elementsState.allocateExpressionId = (tupleId, allocated))
      (resultEq : (inferred, resultState) =
        (⟨tupleId, Ty.productMany (elements.map (·.type))⟩,
          allocated.recordNode (.expression {
            id := tupleId, span, type := Ty.productMany (elements.map (·.type)),
            form := .tuple (elements.map (·.id)) }))) :
      ExpressionHasType semanticSource semanticContext inferred.id
        (finalized.substitution.apply inferred.type) := by
    cases resultEq
    let node : ExpressionNode := {
      id := tupleId, span, type := Ty.productMany (elements.map (·.type)),
      form := .tuple (elements.map (·.id)) }
    have contains : ContainsExpression ((allocated.recordNode (.expression node)).toTypedSource roots) tupleId node :=
      recordNode_containsExpression allocated node
    have edge : ∀ element ∈ elements, DirectChild
        ((allocated.recordNode (.expression node)).toTypedSource roots)
        (.expression tupleId) (.expression element.id) := by
      intro element member
      refine ⟨.expression node, ⟨contains.1, rfl⟩, ?_⟩
      simp only [nodeChildIds, Node.references, node, ExpressionForm.references]
      exact List.mem_map.mpr ⟨element.id, List.mem_map.mpr ⟨element, member, rfl⟩, rfl⟩
    have elementsToParent : TypingSourceExtends (elementsState.toTypedSource roots)
        ((allocated.recordNode (.expression node)).toTypedSource roots) := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      rw [← allocatedEq]
      exact ⟨rfl, ⟨[.expression node], rfl⟩⟩
    have containsFinal := finalPreserved.subgraph.containsExpression
      (FlexibleSubstitution.ContainsExpression.applySubstitution finalized.substitution contains) (.inl rfl)
    have finalEdge : ∀ element ∈ elements, DirectChild finalized.typedSource
        (.expression tupleId) (.expression element.id) := by
      intro element member
      refine ⟨.expression (node.applySubstitution finalized.substitution),
        ⟨containsFinal.1, rfl⟩, ?_⟩
      simpa [nodeChildIds, Node.references, node, ExpressionNode.applySubstitution,
        ExpressionForm.applySubstitution, ExpressionForm.references] using
        (List.mem_map.mpr ⟨element.id, List.mem_map.mpr ⟨element, member, rfl⟩, rfl⟩ :
          NodeId.expression element.id ∈ (elements.map (·.id)).map NodeId.expression)
    have elementsExtension : finalized.substitution.SemanticallyExtends elementsState.inference.substitution := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      have same : allocated.inference.substitution = elementsState.inference.substitution := by
        rw [← allocatedEq]
        rfl
      simpa only [State.recordNode, same] using extension
    have elementPatterns : elementsState.integerPatterns ⊆ evidenceState.integerPatterns := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      have same : allocated.integerPatterns = elementsState.integerPatterns := by
        rw [← allocatedEq]
        rfl
      simpa only [State.recordNode, same] using patterns
    have elementLiterals : elementsState.integerLiterals ⊆ evidenceState.integerLiterals := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      have same : allocated.integerLiterals = elementsState.integerLiterals := by
        rw [← allocatedEq]
        rfl
      simpa only [State.recordNode, same] using literals
    have elementRequirements : elementsState.requirements ⊆ evidenceState.requirements := by
      have allocatedEq : elementsState.allocateExpressionId.2 = allocated := congrArg Prod.snd allocation
      have same : allocated.requirements = elementsState.requirements := by
        rw [← allocatedEq]
        rfl
      simpa only [State.recordNode, same] using requirements
    have typed := actualInferExprsFuelFinalSubtreeSoundness fuel
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self fuel)))
      elementsSuccess resources interfaces elementsExtension signaturesEq ownerEq parametersEq assumptionsEq
      formation functions catalog canonical invariant actual operational
      (fun element member => (semantic.child (edge element member)).monoBefore elementsToParent)
      (fun element member => (finalPreserved.child (edge element member)).monoBefore elementsToParent)
      (fun element member => ((raw.child (edge element member)).monoBefore elementsToParent).proper)
      elementPatterns elementLiterals elementRequirements
      (fun element member => covered.expressionChild resources.graph_closed (finalEdge element member))
      (fun element member => actualCovered.directChild (finalEdge element member))
    have containsSemantic := semantic.subgraph.containsExpression
      (FlexibleSubstitution.ContainsExpression.applySubstitution finalized.substitution contains) (.inl rfl)
    have rawAdmissible : TypeAdmissible semanticContext
        (finalized.substitution.apply (Ty.productMany (elements.map (·.type)))) := by
      simpa [FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using
        typed.product_type_admissible (invariant.typeParameterBinders (by
          simpa [ownerEq, parametersEq] using canonical))
    apply ExpressionHasType.ofOrdinary (owned := []) containsSemantic
    · simpa [node, ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        FlexibleSubstitution.apply_productMany, List.map_map, Function.comp_def] using
        ExpressionFormHasRawType.tuple typed
    · simpa [node, ExpressionNode.applySubstitution, FlexibleSubstitution.apply_productMany,
        List.map_map, Function.comp_def] using rawAdmissible
    · simpa [node, ExpressionNode.applySubstitution, FlexibleSubstitution.apply_productMany,
        List.map_map, Function.comp_def] using rawAdmissible
    · intro requirement member
      simp at member
    · simpa [node, ExpressionNode.applySubstitution, FlexibleSubstitution.apply_productMany,
        List.map_map, Function.comp_def] using
        (CoercionPathValid.nil (context := semanticContext)
          (Ty.productMany (elements.map fun argument => finalized.substitution.apply argument.type)))
    · simp [node, ExpressionNode.applySubstitution, coercionRequirementIds]
  cases sources with
  | nil =>
    unfold inferMatchScrutineesFuel at success
    cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext [] initial with
    | error error => simp [elementsSuccess, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨elements, elementsState⟩ := pair
      simp only [elementsSuccess, bind, Except.bind] at success
      obtain ⟨tupleId, allocated⟩ := elementsState.allocateExpressionId
      exact generated elementsSuccess rfl (Except.ok.inj success).symm
  | cons first rest =>
    cases rest with
    | nil =>
      have childSuccess : Detail.inferExprFuel fuel inferenceContext first none initial = .ok (inferred, resultState) := by
        simpa [inferMatchScrutineesFuel] using success
      exact actualInferExprFuelFinalSubtreeSoundness_of_retainedSoundness
        (recursive fuel (Nat.lt_succ_self fuel)) childSuccess resources interfaces extension
        signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
        (by simp) (by simp) semantic finalPreserved raw.proper patterns literals requirements covered actualCovered
    | cons second rest =>
      unfold inferMatchScrutineesFuel at success
      cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext (first :: second :: rest) initial with
      | error error => simp [elementsSuccess, bind, Except.bind] at success
      | ok pair =>
        obtain ⟨elements, elementsState⟩ := pair
        simp only [elementsSuccess, bind, Except.bind] at success
        obtain ⟨tupleId, allocated⟩ := elementsState.allocateExpressionId
        exact generated elementsSuccess rfl (Except.ok.inj success).symm

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedMatchScrutineeScope
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference

/-- Actual match scrutinee inference preserves the caller's lexical scope,
including the allocation and recording of a generated tuple. -/
theorem inferMatchScrutineesFuel_success_lexicalScope_eq
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {initial : State} {result : InferredExpression × State}
    (success : inferMatchScrutineesFuel fuel context span sources initial = .ok result) :
    result.2.lexicalScope = initial.lexicalScope := by
  have generated {elements : List InferredExpression} {elementsState : State}
      (accepted : Detail.inferExprsFuel fuel context sources initial = .ok (elements, elementsState))
      (recorded : result =
        (⟨elementsState.allocateExpressionId.1, TypeSystem.Ty.productMany (elements.map (·.type))⟩,
          elementsState.allocateExpressionId.2.recordNode (.expression {
            id := elementsState.allocateExpressionId.1, span,
            type := TypeSystem.Ty.productMany (elements.map (·.type)),
            form := .tuple (elements.map (·.id)) }))) :
      result.2.lexicalScope = initial.lexicalScope := by
    rw [recorded]
    exact Detail.inferExprsFuel_success_lexicalScope_eq accepted
  cases sources with
  | nil =>
    unfold inferMatchScrutineesFuel at success
    cases accepted : Detail.inferExprsFuel fuel context [] initial with
    | error error => simp [accepted, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨elements, elementsState⟩ := pair
      simp only [accepted, bind, Except.bind] at success
      exact generated accepted (Except.ok.inj success).symm
  | cons first rest =>
    cases rest with
    | nil =>
      exact Detail.inferExprFuel_success_lexicalScope_eq (by
        simpa [inferMatchScrutineesFuel] using success)
    | cons second rest =>
      unfold inferMatchScrutineesFuel at success
      cases accepted : Detail.inferExprsFuel fuel context (first :: second :: rest) initial with
      | error error => simp [accepted, bind, Except.bind] at success
      | ok pair =>
        obtain ⟨elements, elementsState⟩ := pair
        simp only [accepted, bind, Except.bind] at success
        exact generated accepted (Except.ok.inj success).symm

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPatternEvidence
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend.SourceInference TypeSystem

/-- The complete root record preserves each requirement's owning occurrence. -/
theorem SubtreePreserved.primaryRequirementOccursAt
    {substitution : Substitution} {before after : TypedSource}
    {occurrence : NodeId} {requirement : RequirementId}
    (preserved : SubtreePreserved substitution before after occurrence)
    (occurs : PrimaryRequirementOccursAt (before.applySubstitution substitution)
      occurrence requirement) :
    PrimaryRequirementOccursAt after occurrence requirement := by
  have original : PrimaryRequirementOccursAt before occurrence requirement := by
    simpa using occurs
  obtain ⟨node, member, owned⟩ := List.mem_flatMap.mp original
  have same : node.id = occurrence := by
    cases node with
    | expression expression =>
      obtain ⟨_, _, equality⟩ := List.mem_map.mp owned
      exact congrArg PrimaryRequirementSite.occurrence equality
    | statement statement =>
      obtain ⟨_, _, equality⟩ := List.mem_map.mp owned
      exact congrArg PrimaryRequirementSite.occurrence equality
  exact List.mem_flatMap.mpr ⟨node.applySubstitution substitution,
    preserved.nodes node member (.inl same), by simpa using owned⟩

/-- Match-pattern evidence restricts to the retained statement subtree even
when unrelated earlier expression records have changed during inference. -/
theorem IntegerPatternEvidenceAt.restrictSubtree
    {substitution : Substitution} {before after : TypedSource}
    {context : SourceSemantics.Context} {state : Frontend.SourceInference.State}
    {occurrence : NodeId}
    (preserved : SubtreePreserved substitution before after occurrence)
    (evidence : IntegerPatternEvidenceAt after context substitution state occurrence) :
    IntegerPatternEvidenceAt (before.applySubstitution substitution)
      context substitution state occurrence := by
  constructor
  intro literal resolution origin decoded targetEq requirementEq originMember
    requirementMember occurs
  exact evidence.valid decoded targetEq requirementEq originMember requirementMember
    (preserved.primaryRequirementOccursAt occurs)

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedMatchSoundness
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
end
