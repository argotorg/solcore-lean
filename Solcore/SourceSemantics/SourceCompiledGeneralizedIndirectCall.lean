import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceInferenceGeneralizedExpressionListState
import Solcore.SourceSemantics.SourceInferenceSelectedIndirectCall

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

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
  have argumentsTyped := expressionsRooted checked childFuel
    (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self childFuel)))
    argumentsSuccess interfaces argumentExtension boundary.scope invariant actual operational
    (fun argument member => (rawProper.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    ((Detail.inferExprFuel_integerPatterns_subset calleeSuccess).trans calleePatterns)
    ((Detail.inferExprFuel_integerLiterals_subset calleeSuccess).trans calleeLiterals)
    ((Detail.inferExprFuel_requirements_subset calleeSuccess).trans calleeRequirements)
    (fun argument member => covered.expressionChild resources.graph_closed (boundary.directChildren (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (boundary.directChildren (argumentEdge argument member)))
  have calleeTyped := expressionRooted_of_retained checked
    (recursive childFuel (Nat.lt_succ_self childFuel)) ({
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


end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
