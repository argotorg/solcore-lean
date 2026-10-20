import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedMatchContracts
import Solcore.SourceSemantics.SourceCompiledProvenanceStatementContracts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables SourceInferenceExecution

private theorem binder_assumptions {owner : Resolved.DeclarationId}
    {before after : SourceSemantics.Context} {binders : List TypedBinder}
    (extension : BindersExtend owner before binders after) : after.assumptions = before.assumptions := by
  induction extension with
  | nil => rfl
  | cons head tail ih => cases head; exact ih

private theorem admissible_local {context : SourceSemantics.Context} {type : Ty}
    (typed : TypeAdmissible context type) (binder : TypedBinder) :
    TypeAdmissible (context.withLocal binder.id binder.scheme binder.schemeRequirements) type :=
  StructuralSubstitution.TypeAdmissible.transportContext (source := context)
    (target := context.withLocal binder.id binder.scheme binder.schemeRequirements) rfl rfl rfl rfl rfl typed

private theorem admissible_binders {owner : Resolved.DeclarationId}
    {before after : SourceSemantics.Context} {binders : List TypedBinder} {type : Ty}
    (extension : BindersExtend owner before binders after)
    (typed : TypeAdmissible before type) : TypeAdmissible after type := by
  induction extension with
  | nil => exact typed
  | cons head tail ih =>
    apply ih
    cases head
    exact admissible_local typed _

theorem matchCases_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}
    (descend : ChildClosed callProvenance)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {cases : List Syntax.MatchCase}
    {scrutinee expectedReturn : Ty} {initial : State} {outerScope : LexicalScope}
    {result : Detail.MatchCasesResult} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context} {occurrence : NodeId}
    (here : callProvenance (.matchCases childFuel inferenceContext scrutinee expectedReturn outerScope cases initial result))
    (boundary : MatchCasesBoundary selected childFuel inferenceContext cases scrutinee expectedReturn
      initial outerScope result frames target occurrence)
    (returnSafe : Safe (activeSchemeQuantifiers initial) initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        callProvenance (.statements small inferenceContext bodySource expectedReturn bodyInitial bodyResult) →
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    MatchCasesConclusion selected inferenceContext scrutinee expectedReturn result frames target := by
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  refine ⟨boundary.resultInvariant checked, boundary.actual,
    boundary.operational.ofMatchCases boundary.invariant.ready catalog formation canonical boundary.scrutineeBelow
      boundary.scrutineeSafe boundary.invariant.returnBelow returnSafe boundary.lexicalScope boundary.accepted, ?_⟩
  induction childFuel generalizing cases initial outerScope result with
  | zero =>
    have accepted := boundary.accepted
    simp only [Detail.inferMatchCasesFuel] at accepted
    cases accepted
  | succ childFuel ih =>
    cases cases with
    | nil =>
      have accepted := boundary.accepted
      simp only [Detail.inferMatchCasesFuel, Except.ok.injEq] at accepted
      subst result
      exact ⟨[], .nil _ _ _, rfl⟩
    | cons arm rest =>
      have accepted := boundary.accepted
      unfold Detail.inferMatchCasesFuel at accepted
      cases patternAccepted : Detail.inferMatchPatternFuel childFuel inferenceContext arm.value.pattern scrutinee initial with
      | error error => simp [patternAccepted, bind, Except.bind] at accepted
      | ok pair =>
        obtain ⟨pattern, patternState⟩ := pair
        cases bodyAccepted : Detail.inferStatementsFuel childFuel inferenceContext arm.value.body.value expectedReturn patternState with
        | error error => simp [patternAccepted, bodyAccepted, bind, Except.bind] at accepted
        | ok bodyResult =>
          let tailInput := bodyResult.state.restoreLexicalScope outerScope
          cases tailAccepted : Detail.inferMatchCasesFuel childFuel inferenceContext scrutinee expectedReturn outerScope rest tailInput with
          | error error => simp [patternAccepted, bodyAccepted, tailInput, tailAccepted, bind, Except.bind] at accepted
          | ok tail =>
            simp only [patternAccepted, bodyAccepted, tailInput, tailAccepted, bind, Except.bind,
              pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            subst result
            have patternProperties := Detail.inferMatchPatternFuel_inferenceProperties boundary.invariant.ready
              boundary.scrutineeBelow formation patternAccepted
            have patternNodes := (Detail.inferMatchPatternFuel_occurrenceBoundExtends patternAccepted).nodesBelowNextOccurrence
              boundary.invariant.nodesBelow
            have bodyNodes := (Detail.inferStatementsFuel_occurrenceBoundExtends bodyAccepted).nodesBelowNextOccurrence patternNodes
            have bodyProperties := Detail.inferStatementsFuel_inferenceProperties patternProperties.2.1 formation canonical
              (boundary.invariant.returnBelow.weaken patternProperties.1.next_le) bodyAccepted
            have throughBody := patternProperties.1.trans bodyProperties.1
            have restored : initial.InferenceProgress tailInput ∧ tailInput.InferenceReady := by
              dsimp [tailInput]
              rw [← boundary.lexicalScope]
              exact State.restoreLexicalScope_inferenceProperties boundary.invariant.ready throughBody
            have tailScope : tailInput.lexicalScope = outerScope := by simp [tailInput]
            have tailProperties := Detail.inferMatchCasesFuel_inferenceProperties restored.2 formation canonical
              (boundary.scrutineeBelow.weaken restored.1.next_le)
              (boundary.invariant.returnBelow.weaken restored.1.next_le) tailScope tailAccepted
            have tailExtension := boundary.extension.trans tailProperties.1.substitution_extends
            have bodyExtension : selected.body.finalized.substitution.SemanticallyExtends
                bodyResult.state.inference.substitution := tailExtension
            have patternExtension := bodyExtension.trans bodyProperties.1.substitution_extends
            have tailNodes := State.restoreLexicalScope_preserves_nodesBelowNextOccurrence bodyResult.state outerScope bodyNodes
            have bodySource : TypingSourceExtends (bodyResult.state.toTypedSource (bodyRoots selected))
                (tail.state.toTypedSource (bodyRoots selected)) := by
              constructor
              · have preserved := Detail.inferMatchCasesFuel_preserves_owner tailAccepted
                exact preserved
              · exact Detail.inferMatchCasesFuel_preserves_nodesPrefix tailAccepted List.prefix_rfl tailNodes (Nat.le_refl _)
            have bodyPatterns : bodyResult.state.integerPatterns ⊆ selected.body.returned.integerPatterns := by
              have subset := Detail.inferMatchCasesFuel_integerPatterns_subset tailAccepted
              exact subset.trans boundary.integerPatterns
            have bodyLiterals : bodyResult.state.integerLiterals ⊆ selected.body.returned.integerLiterals := by
              have subset := Detail.inferMatchCasesFuel_integerLiterals_subset tailAccepted
              exact subset.trans boundary.integerLiterals
            have bodyRequirements : bodyResult.state.requirements ⊆ selected.body.returned.requirements := by
              have subset := Detail.inferMatchCasesFuel_requirements_subset tailAccepted
              exact subset.trans boundary.requirements
            have patternMetadata := Detail.inferMatchCasesFuel_headPatternState_metadata_subset
              patternAccepted bodyAccepted boundary.accepted
            let recordedHead : TypedMatchCase := {span := arm.span, pattern, body := bodyResult.statements}
            obtain ⟨certificate, patternInvariant, patternActual, patternOperational⟩ :=
              patternEntered (inferred := pattern) checked boundary.scope (RecursiveExpressionInvariant.ofStatement boundary.invariant)
                boundary.actual boundary.operational boundary.owner boundary.scrutineeBelow boundary.scrutineeAdmissible
                boundary.scrutineeSafe patternExtension (patternMetadata.1.trans boundary.integerPatterns)
                (patternMetadata.2.trans boundary.requirements)
                (fun requirement member => boundary.patternOccurs recordedHead (by exact List.mem_cons_self) requirement member)
                boundary.patternCovered patternAccepted
            have armInvariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized
                patternState certificate.armContext := {
              active := patternInvariant.active
              ready := patternInvariant.ready
              returnBelow := boundary.invariant.returnBelow.weaken patternProperties.1.next_le
              bindersBelow := patternInvariant.bindersBelow
              nodesBelow := patternInvariant.nodesBelow
              schemeIsolation := patternInvariant.schemeIsolation
              substitutionExtension := patternInvariant.substitutionExtension
              signaturesEq := patternInvariant.signaturesEq
              typeParametersEq := patternInvariant.typeParametersEq
              declarationEq := patternInvariant.declarationEq
              residual := patternInvariant.residual
              solvedRequirementsEq := patternInvariant.solvedRequirementsEq
              assumptionsMono := patternInvariant.assumptionsMono }
            have armReturnSafe := boundary.operational.pattern_safe_transport boundary.invariant.ready formation
              boundary.scrutineeBelow boundary.scrutineeSafe returnSafe patternAccepted
            have assumptions := binder_assumptions certificate.binders_extend
            obtain ⟨bodyContext, bodyFacts, bodyInvariant, _, bodyOperational, bodyTyping, bodyAgreement⟩ :=
              recursiveBody childFuel (Nat.lt_succ_self _)
                (descend here (ChildStep.matchCases_body boundary.accepted patternAccepted bodyAccepted))
                (safe_active_iff.mp armReturnSafe)
                (admissible_binders certificate.binders_extend returnAdmissible) ({
                  accepted := bodyAccepted
                  interfaces := boundary.interfaces
                  extension := bodyExtension
                  scope := boundary.scope
                  invariant := armInvariant
                  actual := patternActual
                  operational := patternOperational
                  rawSubtrees := fun child member => (boundary.rawSubtrees recordedHead (by exact List.mem_cons_self) child member).monoBefore bodySource
                  integerPatterns := bodyPatterns
                  integerLiterals := bodyLiterals
                  requirements := bodyRequirements
                  covered := by
                    intro child member owner scopes
                    change owner.requirement.predicate ∈ certificate.armContext.assumptions
                    rw [assumptions]
                    exact boundary.covered recordedHead (by exact List.mem_cons_self) child member owner scopes
                  actualCovered := fun child member => boundary.actualCovered recordedHead (by exact List.mem_cons_self) child member } :
                  StatementsBoundary selected childFuel inferenceContext arm.value.body.value expectedReturn
                    patternState bodyResult frames certificate.armContext)
            let headCertificate : MatchCaseInferenceCertificate selected.body.finalized.typedSource
                {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
                target selected.body.finalized.substitution scrutinee pattern patternState bodyResult := {
              binders := certificate.binders
              rootArity := certificate.rootArity
              armContext := certificate.armContext
              finalContext := bodyContext
              facts := bodyFacts
              pattern_type := certificate.pattern_type
              binders_extend := certificate.binders_extend
              pattern_invariant := certificate.pattern_invariant
              body_type := bodyTyping
              body_matches := bodyAgreement }
            obtain ⟨headFacts, headTyping, headAgreement⟩ := headCertificate.toMatchCaseHasType (arm := arm)
            have tailInvariant : RecursiveStatementInvariant (checkingContext selected) expectedReturn selected.body.finalized
                tailInput target := by
              dsimp [tailInput]
              rw [← boundary.lexicalScope]
              exact boundary.invariant.restoreLexicalScope throughBody bodyInvariant.nodesBelow
                (Nat.le_trans (Detail.inferMatchPatternFuel_nextLocal_le patternAccepted)
                  (Detail.inferStatementsFuel_nextLocal_le bodyAccepted)) bodyExtension
            have patternScope := ProtectedVariables.inferMatchPatternFuel_scope patternAccepted
            have saved : initial.localBinders ⊆ bodyResult.state.localBinders :=
              patternScope.retained.trans (ProtectedVariables.inferStatementsFuel_binders_subset bodyAccepted)
            have tailOperational : GeneralizedActualStateInvariant tailInput (evidenceSource selected) := by
              dsimp [tailInput]
              rw [← boundary.lexicalScope]
              exact bodyOperational.restoreSaved boundary.operational.origins saved
            have patternPrivacy := ProtectedVariables.inferMatchPatternFuel_private boundary.invariant.ready
              boundary.scrutineeBelow formation (activeSchemeQuantifiers_below_next boundary.operational.quantifiersBelow)
              boundary.scrutineeSafe boundary.operational.privacy.all_live patternAccepted
            have bodyPrivacy := ProtectedVariables.inferStatementsFuel_private (activeSchemeQuantifiers initial)
              childFuel inferenceContext arm.value.body.value expectedReturn patternState patternInvariant.ready
              patternOperational.requirements
              (fun v member => Nat.lt_of_lt_of_le
                (activeSchemeQuantifiers_below_next boundary.operational.quantifiersBelow v member) patternProperties.1.next_le)
              patternPrivacy.2.1 catalog formation canonical armInvariant.returnBelow
              (patternPrivacy.1 expectedReturn returnSafe) _ bodyAccepted
            have tailBinders : tailInput.localBinders = initial.localBinders := by
              change outerScope.binders = initial.localBinders
              exact congrArg LexicalScope.binders boundary.lexicalScope.symm
            have tailReturnSafe : Safe (activeSchemeQuantifiers tailInput) tailInput expectedReturn := by
              change Safe (activeSchemeQuantifiers tailInput) bodyResult.state expectedReturn
              rw [activeSchemeQuantifiers, tailBinders]
              exact bodyPrivacy.1 expectedReturn (patternPrivacy.1 expectedReturn returnSafe)
            have tailScrutineeSafe : Safe (activeSchemeQuantifiers tailInput) tailInput scrutinee := by
              change Safe (activeSchemeQuantifiers tailInput) bodyResult.state scrutinee
              rw [activeSchemeQuantifiers, tailBinders]
              exact bodyPrivacy.1 scrutinee (patternPrivacy.1 scrutinee boundary.scrutineeSafe)
            have tailOwner : tailInput.owner = (checkingContext selected).scope.genericOwner :=
              (Detail.inferStatementsFuel_preserves_owner bodyAccepted).trans
                ((Detail.inferMatchPatternFuel_preserves_owner patternAccepted).trans boundary.owner)
            obtain ⟨tailFacts, tailTyping, tailAgreement⟩ := ih
              (descend here (ChildStep.matchCases_tail boundary.accepted patternAccepted bodyAccepted tailAccepted)) ({
              accepted := tailAccepted
              interfaces := boundary.interfaces
              extension := boundary.extension
              scope := boundary.scope
              invariant := tailInvariant
              actual := boundary.actual
              operational := tailOperational
              owner := tailOwner
              lexicalScope := tailScope
              scrutineeBelow := boundary.scrutineeBelow.weaken restored.1.next_le
              scrutineeAdmissible := boundary.scrutineeAdmissible
              scrutineeSafe := tailScrutineeSafe
              integerPatterns := boundary.integerPatterns
              integerLiterals := boundary.integerLiterals
              requirements := boundary.requirements
              patternCovered := boundary.patternCovered
              patternOccurs := fun arm member => boundary.patternOccurs arm (by simp [member])
              rawSubtrees := fun arm member => boundary.rawSubtrees arm (by simp [member])
              covered := fun arm member => boundary.covered arm (by simp [member])
              actualCovered := fun arm member => boundary.actualCovered arm (by simp [member]) } :
              MatchCasesBoundary selected childFuel inferenceContext rest scrutinee expectedReturn
                tailInput outerScope tail frames target occurrence) tailReturnSafe
              (fun small bound => recursiveBody small (Nat.lt_trans bound (Nat.lt_succ_self _)))
            refine ⟨headFacts :: tailFacts, ?_, ?_⟩
            · simpa only [List.map_cons] using MatchCasesHaveType.cons headTyping tailTyping
            · change (headFacts.sawReturn && allBodiesSawReturn tailFacts) = (bodyResult.sawReturn && tail.allReturn)
              rw [headAgreement.sawReturn_eq, tailAgreement]

theorem matchCases
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {cases : List Syntax.MatchCase}
    {scrutinee expectedReturn : Ty} {initial : State} {outerScope : LexicalScope}
    {result : Detail.MatchCasesResult} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context} {occurrence : NodeId}
    (boundary : MatchCasesBoundary selected childFuel inferenceContext cases scrutinee expectedReturn
      initial outerScope result frames target occurrence)
    (returnSafe : Safe (activeSchemeQuantifiers initial) initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ small, small < childFuel →
      ∀ {bodySource : List Syntax.Statement} {bodyInitial : State} {bodyResult : Detail.BlockResult}
        {bodyTarget : SourceSemantics.Context},
        (∀ binder ∈ bodyInitial.localBinders, Safe binder.scheme.quantified bodyInitial expectedReturn) →
        TypeAdmissible bodyTarget (selected.body.finalized.substitution.apply expectedReturn) →
        StatementsBoundary selected small inferenceContext bodySource expectedReturn bodyInitial bodyResult frames bodyTarget →
        StatementsConclusion selected inferenceContext expectedReturn bodyResult frames bodyTarget) :
    MatchCasesConclusion selected inferenceContext scrutinee expectedReturn result frames target := by
  exact matchCases_for (callProvenance := fun _ => True) true_childClosed checked True.intro
    boundary returnSafe returnAdmissible (fun small less => by
      intro bodySource bodyInitial bodyResult bodyTarget _
      exact recursiveBody small less)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
