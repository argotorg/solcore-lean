import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedRetainedExpressionList
import Solcore.SourceSemantics.SourceInferenceSelectedCandidateCall
import Solcore.SourceSemantics.SourceInferenceSelectedOperatorMetadata

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

/-- Candidate selection and argument attachment consume the actual retained
argument proofs in the same selected final source. -/
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
  have argumentBases := expressionsRetainedBases checked childFuel recursive argumentsSuccess
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

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
