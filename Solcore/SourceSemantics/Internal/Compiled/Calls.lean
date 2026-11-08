import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.Internal.Selected.Calls
import Solcore.SourceSemantics.Internal.Compiled.InitializerOccurrences
import Solcore.SourceSemantics.Internal.Selected.Candidates
import Solcore.SourceSemantics.Internal.Selected.OperatorMetadata

/-!
# Named and indirect calls

Candidate selection, indirect application and constructor arguments consume the retained argument
proofs in the same selected source.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedConstructorArguments
/-! Constructor arguments use the expected payload types from the actual
constructor instantiation. Each child is checked in the selected final source
and preserves the incoming generalized scope. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem constructorArgumentsRooted_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRetainedSoundnessFor callProvenance selected childFuel) :
    ∀ {inferenceContext : SourceInference.Context} {sources : List Syntax.Expr}
      {expectedTypes : List Ty} {initial resultState : State}
      {inferred : List InferredExpression}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    callProvenance (.constructorArguments childFuel inferenceContext sources expectedTypes initial inferred resultState) →
    Detail.inferConstructorArgumentsFuel childFuel inferenceContext sources expectedTypes initial =
      .ok (inferred, resultState) →
    ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource →
    selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    CheckingScope selected inferenceContext →
    RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target →
    ActualContext (checkingContext selected) selected.body.finalized frames target →
    GeneralizedActualStateInvariant initial (evidenceSource selected) →
    (∀ type ∈ expectedTypes, type.VariablesBelow initial.inference.next) →
    (∀ type ∈ expectedTypes, TypeAdmissible target (selected.body.finalized.substitution.apply type)) →
    (∀ binder ∈ initial.localBinders, ∀ type ∈ expectedTypes,
      ProtectedVariables.Safe binder.scheme.quantified initial type) →
    (∀ argument ∈ inferred, RawSubtreePreserved (resultState.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.expression argument.id)) →
    resultState.integerPatterns ⊆ selected.body.returned.integerPatterns →
    resultState.integerLiterals ⊆ selected.body.returned.integerLiterals →
    resultState.requirements ⊆ selected.body.returned.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers selected.body.finalized frames (.expression argument.id)) →
    ExpressionsHaveTypes selected.body.finalized.typedSource target (inferred.map (·.id))
      (expectedTypes.map selected.body.finalized.substitution.apply) := by
  intro inferenceContext sources
  induction sources with
  | nil =>
    intro expectedTypes initial resultState inferred frames target here accepted
    cases expectedTypes with
    | nil =>
      simp only [Detail.inferConstructorArgumentsFuel, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      intros
      exact .nil target
    | cons _ _ => simp [Detail.inferConstructorArgumentsFuel] at accepted
  | cons source sources induction =>
    intro expectedTypes initial resultState inferred frames target here accepted interfaces extension scope
      invariant actual operational expectedBelow expectedAdmissible expectedSafe rawPreserved
      integerPatternsSubset integerLiteralsSubset requirementsSubset covered actualCovered
    cases expectedTypes with
    | nil => simp [Detail.inferConstructorArgumentsFuel] at accepted
    | cons expected expectedTypes =>
      have formation := scope.formation checked
      have functions := scope.functionsCanonical checked
      have catalog := scope.catalog checked
      have parentAccepted := accepted
      unfold Detail.inferConstructorArgumentsFuel at accepted
      cases headSuccess : Detail.inferExprFuel childFuel inferenceContext source
          (some (initial.resolve expected)) initial with
      | error error => simp [headSuccess, bind, Except.bind] at accepted
      | ok pair =>
        obtain ⟨head, headState⟩ := pair
        simp only [headSuccess, bind, Except.bind] at accepted
        cases tailSuccess : Detail.inferConstructorArgumentsFuel childFuel inferenceContext
            sources expectedTypes headState with
        | error error => simp [tailSuccess] at accepted
        | ok pair =>
          obtain ⟨tail, tailState⟩ := pair
          simp only [tailSuccess, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          have headExpectedBelow : ∀ type ∈ some (initial.resolve expected),
              type.VariablesBelow initial.inference.next := by
            intro type member
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using member.symm
            subst type
            exact invariant.ready.solved.variablesBelow_apply (expectedBelow expected (by simp))
          have headExpectedSafe : ∀ binder ∈ initial.localBinders,
              ∀ type ∈ some (initial.resolve expected),
              ProtectedVariables.Safe binder.scheme.quantified initial type := by
            intro binder member type typeMember
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using typeMember.symm
            subst type
            exact ProtectedVariables.safe_resolved invariant.ready
              (expectedSafe binder member expected (by simp))
          have headProperties := Detail.inferExprFuel_inferenceProperties invariant.ready formation
            functions headExpectedBelow headSuccess
          have tailExpectedBelow : ∀ type ∈ expectedTypes, type.VariablesBelow headState.inference.next :=
            fun type member => (expectedBelow type (by simp [member])).weaken headProperties.1.next_le
          have tailProperties := Detail.inferConstructorArgumentsFuel_inferenceProperties
            headProperties.2.1 formation functions tailExpectedBelow tailSuccess
          have headExtension := extension.trans tailProperties.1.substitution_extends
          have initialExtension := headExtension.trans headProperties.1.substitution_extends
          have initialResolved : selected.body.finalized.substitution.apply (initial.resolve expected) =
              selected.body.finalized.substitution.apply expected := by
            simpa only [State.resolve, InferState.resolve] using initialExtension expected
          have headExpectedAdmissible : ∀ type ∈ some (initial.resolve expected),
              TypeAdmissible target (selected.body.finalized.substitution.apply type) := by
            intro type member
            have same : type = initial.resolve expected := by
              simpa only [Option.mem_def, Option.some.injEq] using member.symm
            rw [same, initialResolved]
            exact expectedAdmissible expected (by simp)
          have headInvariant := invariant.ofExpression formation functions headExpectedBelow
            headExtension headSuccess
          have headOperational := operational.ofExpression invariant.ready catalog formation functions
            headExpectedBelow headExpectedSafe headSuccess
          have headToFinal := inferConstructorArgumentsFuel_success_typingSourceExtends
            tailSuccess headInvariant.nodesBelow (bodyRoots selected)
          have headHere := descend here (.constructorArguments_head parentAccepted headSuccess)
          have tailHere := descend here (.constructorArguments_tail parentAccepted headSuccess tailSuccess)
          have headTyped := expressionRooted_of_retained_for checked recursive headHere ({
            accepted := headSuccess
            interfaces := interfaces
            extension := headExtension
            scope := scope
            invariant := invariant
            actual := actual
            operational := operational
            expectedBelow := headExpectedBelow
            expectedAdmissible := headExpectedAdmissible
            expectedSafe := headExpectedSafe
            integerPatterns := (Detail.inferConstructorArgumentsFuel_integerPatterns_subset tailSuccess).trans
              integerPatternsSubset
            integerLiterals := (Detail.inferConstructorArgumentsFuel_integerLiterals_subset tailSuccess).trans
              integerLiteralsSubset
            requirements := (Detail.inferConstructorArgumentsFuel_requirements_subset tailSuccess).trans
              requirementsSubset
            covered := covered head (by simp)
            actualCovered := actualCovered head (by simp)
            rawSubtree := (rawPreserved head (by simp)).monoBefore headToFinal } :
            RootedExpressionBoundary selected childFuel inferenceContext source
              (some (initial.resolve expected)) initial head headState frames target)
          have headTypeEq : selected.body.finalized.substitution.apply head.type =
              selected.body.finalized.substitution.apply expected :=
            (Detail.inferExprFuel_expected_type_apply_eq headSuccess headExtension).trans initialResolved
          have tailSafe : ∀ binder ∈ headState.localBinders, ∀ type ∈ expectedTypes,
              ProtectedVariables.Safe binder.scheme.quantified headState type := by
            have binders : headState.localBinders = initial.localBinders :=
              congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq headSuccess)
            intro binder member type typeMember
            have old := binders ▸ member
            have privacy := ProtectedVariables.inferExprFuel_private binder.scheme.quantified childFuel
              inferenceContext source (some (initial.resolve expected)) initial invariant.ready
              operational.requirements (operational.quantifiersBelow binder old)
              (operational.privacy binder old) catalog formation functions headExpectedBelow
              (headExpectedSafe binder old) _ headSuccess
            exact privacy.1 type (expectedSafe binder old type (by simp [typeMember]))
          have tailTyped := induction tailHere tailSuccess interfaces extension scope headInvariant actual
            headOperational tailExpectedBelow
            (fun type member => expectedAdmissible type (by simp [member])) tailSafe
            (fun argument member => rawPreserved argument (by simp [member]))
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            (fun argument member => covered argument (by simp [member]))
            (fun argument member => actualCovered argument (by simp [member]))
          exact .cons (by simpa only [headTypeEq] using headTyped) tailTyped

theorem constructorArgumentsRooted
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRetainedSoundness selected childFuel) :
    ∀ {inferenceContext : SourceInference.Context} {sources : List Syntax.Expr}
      {expectedTypes : List Ty} {initial resultState : State}
      {inferred : List InferredExpression}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    Detail.inferConstructorArgumentsFuel childFuel inferenceContext sources expectedTypes initial =
      .ok (inferred, resultState) →
    ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
      selected.body.finalized.solvedRequirements selected.body.finalized.typedSource →
    selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution →
    CheckingScope selected inferenceContext →
    RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target →
    ActualContext (checkingContext selected) selected.body.finalized frames target →
    GeneralizedActualStateInvariant initial (evidenceSource selected) →
    (∀ type ∈ expectedTypes, type.VariablesBelow initial.inference.next) →
    (∀ type ∈ expectedTypes, TypeAdmissible target (selected.body.finalized.substitution.apply type)) →
    (∀ binder ∈ initial.localBinders, ∀ type ∈ expectedTypes,
      ProtectedVariables.Safe binder.scheme.quantified initial type) →
    (∀ argument ∈ inferred, RawSubtreePreserved (resultState.toTypedSource (bodyRoots selected))
      (evidenceSource selected) (.expression argument.id)) →
    resultState.integerPatterns ⊆ selected.body.returned.integerPatterns →
    resultState.integerLiterals ⊆ selected.body.returned.integerLiterals →
    resultState.requirements ⊆ selected.body.returned.requirements →
    (∀ argument ∈ inferred, TemplateScopeCovered selected.body.finalized.typedSource target
      (.expression argument.id)) →
    (∀ argument ∈ inferred, ActualContext.Covers selected.body.finalized frames (.expression argument.id)) →
    ExpressionsHaveTypes selected.body.finalized.typedSource target (inferred.map (·.id))
      (expectedTypes.map selected.body.finalized.substitution.apply) := by
  intro inferenceContext sources expectedTypes initial resultState inferred frames target accepted
  exact constructorArgumentsRooted_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro accepted

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedIndirectCall
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem indirectCall_typing_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel parentFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {expression calleeSource : Syntax.Expr}
    {expected : Option Ty} {parentInitial initial argumentState calleeState resultState : State}
    {inferred callee : InferredExpression} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {call : ExpressionId} {application : Detail.IndirectApplicationResult}
    (boundary : RetainedExpressionBoundary selected parentFuel inferenceContext expression expected
      parentInitial inferred resultState frames target)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (argumentsHere : callProvenance (.expressions childFuel inferenceContext argumentSources initial arguments argumentState))
    (argumentsSuccess : Detail.inferExprsFuel childFuel inferenceContext argumentSources initial =
      .ok (arguments, argumentState))
    (calleeHere : callProvenance (.expression childFuel inferenceContext calleeSource none argumentState callee calleeState))
    (calleeSuccess : Detail.inferExprFuel childFuel inferenceContext calleeSource none argumentState =
      .ok (callee, calleeState))
    (applicationSuccess : Detail.applyFunctionType inferenceContext call callee.type arguments expected
      calleeState = .ok application)
    (recording : Detail.recordIndirectCall expression callee arguments application = (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  let wholeContext := checkingContext selected
  let finalized := selected.body.finalized
  let roots := bodyRoots selected
  let evidenceState := selected.body.returned
  let semanticContext := target
  have resources := selected.body.resources
  have interfaces := boundary.interfaces
  have resultSubstitutionExtension := boundary.extension
  have signaturesEq := boundary.scope.signatures
  have signatureFormation := boundary.scope.formation checked
  have functionsCanonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have actual := boundary.actual
  have rawProper := boundary.rawProper
  have integerPatternsSubset := boundary.integerPatterns
  have integerLiteralsSubset := boundary.integerLiterals
  have requirementsSubset := boundary.requirements
  have covered := boundary.covered
  have actualCovered := boundary.actualCovered
  have inferredEq : inferred = application.result := by
    have same := congrArg Prod.fst recording
    simpa only [Detail.recordIndirectCall_fst] using same.symm
  subst inferred
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have calleeProperties := Detail.inferExprFuel_inferenceProperties argumentProperties.2.1
    signatureFormation functionsCanonical (by simp) calleeSuccess
  have argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow calleeState.inference.next :=
    fun argument member => (argumentProperties.2.2 argument member).weaken calleeProperties.1.next_le
  have expectedAtCallee : ∀ type ∈ expected, type.VariablesBelow calleeState.inference.next :=
    fun type member => (expectedBelow type member).weaken (argumentProperties.1.trans calleeProperties.1).next_le
  have applicationProperties := Detail.applyFunctionType_inferenceProperties
    calleeProperties.2.1 calleeProperties.2.2 argumentsBelow expectedAtCallee applicationSuccess
  have recordProperties := Detail.recordIndirectCall_inferenceProperties expression callee arguments application
    applicationProperties.2.1 applicationProperties.2.2
  rw [recording] at recordProperties
  have applicationExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have calleeExtension := applicationExtension.trans applicationProperties.1.substitution_extends
  have argumentExtension := calleeExtension.trans calleeProperties.1.substitution_extends
  have argumentInvariant := invariant.ofExpressions signatureFormation functionsCanonical argumentExtension argumentsSuccess
  have argumentOperational := operational.ofExpressions invariant.ready catalog signatureFormation functionsCanonical argumentsSuccess
  have argumentToCallee := inferExprFuel_success_typingSourceExtends calleeSuccess argumentInvariant.nodesBelow roots
  have metadata := applyFunctionType_metadata applicationSuccess
  have calleeToApplication : TypingSourceExtends (calleeState.toTypedSource roots)
      (application.state.toTypedSource roots) := by
    refine ⟨metadata.1, ?_⟩
    change calleeState.nodes <+: application.state.nodes
    rw [(Detail.applyFunctionType_occurrenceState_eq applicationSuccess).1]
    exact List.prefix_rfl
  have applicationToParent : TypingSourceExtends (application.state.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    refine ⟨rfl, ?_⟩
    change application.state.nodes <+: application.state.nodes ++ [_]
    exact List.prefix_append _ _
  have calleeToParent := calleeToApplication.trans applicationToParent
  have argumentToParent := argumentToCallee.trans calleeToParent
  let callMetadata : IndirectCallResolution := {
    argumentCount := arguments.length
    argumentTypeBeforeCoercion := Ty.productMany (arguments.map (·.type))
    argumentTypeAfterCoercion := application.argumentCoercions.foldl
      (fun _ step => step.target) (Ty.productMany (arguments.map (·.type)))
    argumentCoercions := application.argumentCoercions
  }
  let callNode : ExpressionNode := {
    id := application.result.id
    span := expression.span
    type := application.result.type
    form := .call callee.id (arguments.map (·.id)) (.indirect callMetadata)
    requirements := Detail.coercionRequirements application.argumentCoercions ++
      Detail.coercionRequirements application.callCoercions
    coercions := application.callCoercions
  }
  have callContains : ContainsExpression (resultState.toTypedSource roots) application.result.id callNode := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    exact recordExpression_containsExpression expression application.result
      (.call callee.id (arguments.map (·.id)) (.indirect callMetadata))
      (Detail.coercionRequirements application.argumentCoercions ++ Detail.coercionRequirements application.callCoercions)
      application.callCoercions application.state roots
  have calleeEdge : DirectChild (resultState.toTypedSource roots) (.expression application.result.id) (.expression callee.id) := by
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp [callNode, nodeChildIds, Node.references, ExpressionForm.references]
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression application.result.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [callNode, nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have parentPatterns : resultState.integerPatterns = application.state.integerPatterns := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    rfl
  have parentLiterals : resultState.integerLiterals = application.state.integerLiterals := by
    have stateEq : (Detail.recordIndirectCall expression callee arguments application).2 = resultState := congrArg Prod.snd recording
    rw [← stateEq]
    rfl
  have calleePatterns : calleeState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← metadata.2.1, ← parentPatterns]
    exact integerPatternsSubset
  have calleeLiterals : calleeState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← metadata.2.2, ← parentLiterals]
    exact integerLiteralsSubset
  have calleeRequirements : calleeState.requirements ⊆ evidenceState.requirements := by
    apply List.Subset.trans (Detail.applyFunctionType_requirements_subset applicationSuccess)
    have recorded := Detail.recordIndirectCall_requirements_subset expression callee arguments application
    rw [recording] at recorded
    exact recorded.trans requirementsSubset
  have argumentsTyped := expressionsRooted_for checked descend childFuel
    (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
    argumentsHere argumentsSuccess interfaces argumentExtension boundary.scope invariant actual operational
    (fun argument member => (rawProper.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    ((Detail.inferExprFuel_integerPatterns_subset calleeSuccess).trans calleePatterns)
    ((Detail.inferExprFuel_integerLiterals_subset calleeSuccess).trans calleeLiterals)
    ((Detail.inferExprFuel_requirements_subset calleeSuccess).trans calleeRequirements)
    (fun argument member => covered.expressionChild resources.graph_closed (boundary.directChildren (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (boundary.directChildren (argumentEdge argument member)))
  have calleeTyped := expressionRooted_of_retained_for checked
    (recursive childFuel (Nat.lt_succ_self childFuel)) calleeHere ({
      accepted := calleeSuccess
      interfaces := interfaces
      extension := calleeExtension
      scope := boundary.scope
      invariant := argumentInvariant
      actual := actual
      operational := argumentOperational
      expectedBelow := by simp
      expectedAdmissible := by simp
      expectedSafe := by simp
      integerPatterns := calleePatterns
      integerLiterals := calleeLiterals
      requirements := calleeRequirements
      covered := covered.expressionChild resources.graph_closed (boundary.directChildren calleeEdge)
      actualCovered := actualCovered.directChild (boundary.directChildren calleeEdge)
      rawSubtree := (rawProper.childSubtree calleeEdge).monoBefore calleeToParent } :
      RootedExpressionBoundary selected childFuel inferenceContext calleeSource none
        argumentState callee calleeState frames target)
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [activeSignaturesEq]
    exact catalog
  have finalSubstitutionEq := resources.substitution_eq.symm
  have finalRequirements : resultState.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact requirementsSubset
  simpa only [finalSubstitutionEq] using
    (applyFunctionType_recordIndirectCall_typing_from_interfaces
      (solverContext := wholeContext) (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      applicationSuccess recording calleeProperties.2.1 calleeProperties.2.2 argumentsBelow expectedAtCallee
      (by simpa only [finalSubstitutionEq] using resultSubstitutionExtension)
      finalRequirements boundary.expressionRequirements boundary.coercionPrimaries (by simpa only [signaturesEq] using interfaces)
      (by simpa only [finalSubstitutionEq] using argumentsTyped)
      (by simpa only [finalSubstitutionEq] using calleeTyped)
      activeCatalog activeSignaturesEq resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered)


theorem indirectCall_typing
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel parentFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {expression calleeSource : Syntax.Expr}
    {expected : Option Ty} {parentInitial initial argumentState calleeState resultState : State}
    {inferred callee : InferredExpression} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {call : ExpressionId} {application : Detail.IndirectApplicationResult}
    (boundary : RetainedExpressionBoundary selected parentFuel inferenceContext expression expected
      parentInitial inferred resultState frames target)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (argumentsSuccess : Detail.inferExprsFuel childFuel inferenceContext argumentSources initial =
      .ok (arguments, argumentState))
    (calleeSuccess : Detail.inferExprFuel childFuel inferenceContext calleeSource none argumentState =
      .ok (callee, calleeState))
    (applicationSuccess : Detail.applyFunctionType inferenceContext call callee.type arguments expected
      calleeState = .ok application)
    (recording : Detail.recordIndirectCall expression callee arguments application = (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact indirectCall_typing_for (callProvenance := fun _ => True) checked true_childClosed
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary)
    boundary invariant operational expectedBelow True.intro argumentsSuccess True.intro calleeSuccess applicationSuccess recording

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedNamedCall
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

/-- Candidate selection and argument attachment consume the actual retained
argument proofs in the same selected final source. -/
theorem selectedCall_typing_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel parentFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {provenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel → ExpressionRetainedSoundnessFor provenance selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {expected : Option Ty} {parentInitial initial argumentState resultState : State}
    {inferred : InferredExpression} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {candidates : List ProgramFunctionSignature}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {attempt : Detail.CandidateAttemptResult}
    (boundary : RetainedExpressionBoundary selected parentFuel inferenceContext expression expected
      parentInitial inferred resultState frames target)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (argumentCalls : OrderedExpressionCalls provenance inferenceContext childFuel
      argumentSources initial arguments argumentState)
    (argumentsSuccess : Detail.inferExprsFuel childFuel inferenceContext argumentSources initial =
      .ok (arguments, argumentState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext name candidates arguments
      integerLiteralOrigins call expected argumentState = .ok attempt)
    (recording : Detail.recordSelectedCall expression callee name arguments attempt = (inferred, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  let wholeContext := checkingContext selected
  let finalized := selected.body.finalized
  let roots := bodyRoots selected
  let evidenceState := selected.body.returned
  let semanticSource := selected.body.finalized.typedSource
  let semanticContext := target
  have resources := selected.body.resources
  have interfaces := boundary.interfaces
  have resultSubstitutionExtension := boundary.extension
  have signaturesEq := boundary.scope.signatures
  have ownerEq := boundary.scope.owner
  have typeParametersEq := boundary.scope.parameters
  have signatureFormation := boundary.scope.formation checked
  have functionsCanonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have canonical := boundary.scope.canonical checked
  have actual := boundary.actual
  have finalPreserved := boundary.proper
  have semanticPreserved := boundary.proper
  have rawProper := boundary.rawProper
  have integerPatternsSubset := boundary.integerPatterns
  have integerLiteralsSubset := boundary.integerLiterals
  have requirementsSubset := boundary.requirements
  have covered := boundary.covered
  have actualCovered := boundary.actualCovered
  have recordSuccess : Detail.recordSelectedCallResult expression callee name arguments attempt
      attempt.result [] attempt.state = (inferred, resultState) := by
    simpa only [Detail.recordSelectedCall] using recording
  have inferredEq : inferred = attempt.result := (Detail.recordSelectedCallResult_success_nodes recordSuccess).1
  subst inferred
  have activeSignaturesEq := invariant.signatures_eq_whole.trans signaturesEq.symm
  obtain ⟨signature, _, signatureMember, signatureCanonical, schemeBelow, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_semanticCandidate signatureFormation functionsCanonical
      activeSignaturesEq candidatesSubset selectionSuccess
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
    fun type member => (expectedBelow type member).weaken argumentProperties.1.next_le
  have candidateProperties := Detail.tryFunctionCandidate_some_inferenceProperties
    argumentProperties.2.1 argumentProperties.2.2 schemeBelow expectedAtArguments candidateSuccess
  have recordProperties := Detail.recordSelectedCall_inferenceProperties expression callee name arguments
    attempt candidateProperties.2.1 candidateProperties.2.2
  rw [recording] at recordProperties
  have attemptExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have argumentExtension := attemptExtension.trans candidateProperties.1.substitution_extends
  have argumentIdsUnique := Detail.inferExprsFuel_success_ids_nodup argumentsSuccess
  have entryIds : attempt.argumentCoercions.map (·.expression) = arguments.map (·.id) :=
    Detail.tryFunctionCandidate_some_argumentCoercion_expression_ids signatureCanonical candidateSuccess
  have entryIdsUnique : (attempt.argumentCoercions.map (·.expression)).Nodup := by
    rw [entryIds]; exact argumentIdsUnique
  have argumentToAttempt : TypingSourceExtends (argumentState.toTypedSource roots)
      (attempt.state.toTypedSource roots) := by
    refine ⟨?_, ?_⟩
    · exact congrArg State.Header.owner (Detail.SelectedMetadata.tryFunctionCandidate_some_state_header candidateSuccess)
    · change argumentState.nodes <+: attempt.state.nodes
      rw [(Detail.tryFunctionCandidate_some_occurrenceState_eq candidateSuccess).1]
      exact List.prefix_rfl
  have attachedExtension := recordSelectedCallResult_success_attachedTypingSourceExtends recordSuccess roots
  have callContains := recordSelectedCallResult_success_containsExpression recordSuccess roots
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression attempt.result.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression _, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have entryEdge : ∀ entry ∈ attempt.argumentCoercions,
      DirectChild (resultState.toTypedSource roots) (.expression attempt.result.id) (.expression entry.expression) := by
    intro entry member
    have idMember : entry.expression ∈ arguments.map (·.id) := by
      rw [← entryIds]; exact List.mem_map.mpr ⟨entry, member, rfl⟩
    obtain ⟨argument, argumentMember, idEq⟩ := List.mem_map.mp idMember
    rw [← idEq]; exact argumentEdge argument argumentMember
  have argumentPreserved : ∀ argument ∈ arguments,
      AttachedChildPreserved finalized.substitution (argumentState.toTypedSource roots)
        semanticSource finalized.typedSource (evidenceState.toTypedSource roots) argument.id := by
    intro argument member
    have idMember : argument.id ∈ attempt.argumentCoercions.map (·.expression) := by
      rw [entryIds]; exact List.mem_map.mpr ⟨argument, member, rfl⟩
    obtain ⟨entry, entryMember, idEq⟩ := List.mem_map.mp idMember
    rw [← idEq]
    exact (AttachedChildPreserved.of_attachment attempt.state attempt.argumentCoercions roots
      attachedExtension entryIdsUnique entryEdge semanticPreserved finalPreserved rawProper
      boundary.directChildren resources.graph_closed entry entryMember).monoBefore argumentToAttempt
  have attemptRequirements := Detail.recordSelectedCall_requirements_subset expression callee name arguments attempt
  rw [recording] at attemptRequirements
  have argumentRequirements := (Detail.tryFunctionCandidate_requirements_subset candidateSuccess).trans
    (attemptRequirements.trans requirementsSubset)
  have argumentPatterns : argumentState.integerPatterns ⊆ evidenceState.integerPatterns := by
    have recordedPatterns := Detail.SelectedMetadata.recordSelectedCallResult_integerPatterns_eq
      expression callee name arguments attempt attempt.result [] attempt.state
    rw [recordSuccess, Detail.SelectedMetadata.tryFunctionCandidate_integerPatterns_eq candidateSuccess] at recordedPatterns
    rw [← recordedPatterns]
    exact integerPatternsSubset
  have argumentLiterals : argumentState.integerLiterals ⊆ evidenceState.integerLiterals := by
    have recordedLiterals := Detail.SelectedMetadata.recordSelectedCallResult_integerLiterals_eq
      expression callee name arguments attempt attempt.result [] attempt.state
    rw [recordSuccess, Detail.SelectedMetadata.tryFunctionCandidate_integerLiterals_eq candidateSuccess] at recordedLiterals
    rw [← recordedLiterals]
    exact integerLiteralsSubset
  have argumentBases := expressionsRetainedBases_for checked childFuel recursive argumentCalls argumentsSuccess
    interfaces argumentExtension boundary.scope invariant actual operational argumentPreserved
    argumentPatterns argumentLiterals argumentRequirements
    (fun argument member => covered.expressionChild resources.graph_closed (boundary.directChildren (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (boundary.directChildren (argumentEdge argument member)))
  have argumentSemantic : ExpressionNodesPreservedAt (arguments.map (·.id))
      (((Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).toTypedSource roots).applySubstitution finalized.substitution)
      semanticSource := by
    intro id node member contains
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
    exact ((semanticPreserved.childSubtree (argumentEdge argument argumentMember)).monoBefore attachedExtension).expressionNode
      (by simp) contains
  have argumentFinal : ExpressionNodesPreservedAt (arguments.map (·.id))
      (((Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).toTypedSource roots).applySubstitution finalized.substitution)
      finalized.typedSource := by
    intro id node member contains
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp member
    exact ((finalPreserved.childSubtree (argumentEdge argument argumentMember)).monoBefore attachedExtension).expressionNode
      (by simp) contains
  have calleeEdge : DirectChild (resultState.toTypedSource roots) (.expression attempt.result.id)
      (.expression (Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).allocateExpressionId.1) := by
    refine ⟨.expression _, ⟨callContains.1, rfl⟩, ?_⟩
    simp [nodeChildIds, Node.references, ExpressionForm.references]
  have calleeSemantic : ExpressionNodesPreservedAt
      [(Detail.attachExpressionCoercions attempt.state attempt.argumentCoercions).allocateExpressionId.1]
      ((resultState.toTypedSource roots).applySubstitution finalized.substitution) semanticSource :=
    (semanticPreserved.childSubtree calleeEdge).expressionNode
  have binders := invariant.typeParameterBinders (by simpa [ownerEq, typeParametersEq] using canonical)
  have range := resources.substitutionRangeAdmissible binders invariant.signatures_eq_whole
    invariant.typeParametersEq invariant.declarationEq invariant.residual
  have activeCatalog : SignatureCatalogWellFormed semanticContext.signatures := by
    rw [activeSignaturesEq]; exact catalog
  have finalSubstitutionEq := resources.substitution_eq.symm
  have finalExtension : resources.finalState.inference.substitution.SemanticallyExtends attempt.state.inference.substitution := by
    simpa only [finalSubstitutionEq] using attemptExtension
  have finalRequirements : attempt.state.requirements ⊆ resources.finalState.requirements := by
    rw [resources.requirements_eq]
    exact attemptRequirements.trans requirementsSubset
  simpa only [finalSubstitutionEq] using
    (tryFunctionCandidate_recordSelectedCallResult_typing_from_interfaces
      (solverContext := wholeContext) (later := resources.finalState)
      (base := finalizedRequirementContext wholeContext finalized)
      signatureCanonical candidateSuccess recordSuccess rfl rfl
      (by simpa only [finalSubstitutionEq] using argumentBases) argumentIdsUnique
      argumentProperties.2.1 argumentProperties.2.2 schemeBelow expectedAtArguments
      finalExtension finalExtension finalRequirements
      (by
        intro id node member found
        apply argumentSemantic member
        simpa only [finalSubstitutionEq] using found)
      (by
        intro id node member found
        apply calleeSemantic member
        simpa only [finalSubstitutionEq] using found)
      (by
        intro id node member found
        apply argumentFinal member
        simpa only [finalSubstitutionEq] using found)
      boundary.expressionRequirements (by simpa only [signaturesEq] using interfaces) boundary.coercionPrimaries
      (fun entry member => covered.expressionChild resources.graph_closed (boundary.directChildren (entryEdge entry member)))
      activeCatalog binders invariant.residual (by simpa only [finalSubstitutionEq] using range)
      signatureMember activeSignaturesEq resources.solve_success resources.solved_context_eq
      resources.ledger resources.ownership invariant.signaturesEq invariant.solvedRequirementsEq
      invariant.assumptionsMono covered (.nil _))

/-- The previous API supplies unrestricted head provenance from actual argument inference. -/
theorem selectedCall_typing
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel parentFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {expected : Option Ty} {parentInitial initial argumentState resultState : State}
    {inferred : InferredExpression} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {candidates : List ProgramFunctionSignature}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {attempt : Detail.CandidateAttemptResult}
    (boundary : RetainedExpressionBoundary selected parentFuel inferenceContext expression expected
      parentInitial inferred resultState frames target)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (argumentsSuccess : Detail.inferExprsFuel childFuel inferenceContext argumentSources initial =
      .ok (arguments, argumentState))
    (selectionSuccess : Detail.selectFunctionCandidateFrom inferenceContext name candidates arguments
      integerLiteralOrigins call expected argumentState = .ok attempt)
    (recording : Detail.recordSelectedCall expression callee name arguments attempt = (inferred, resultState))
    (candidatesSubset : candidates ⊆ inferenceContext.signatures.functions) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact selectedCall_typing_for (provenance := fun _ => True) checked
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary)
    boundary invariant operational expectedBelow (OrderedExpressionCalls.of_accepted argumentsSuccess)
    argumentsSuccess selectionSuccess recording candidatesSubset

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end
