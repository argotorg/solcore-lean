import Solcore.SourceSemantics.Internal.Prepared.TemplateInventory
import Solcore.SourceSemantics.Internal.Compiled.Finalization
import Solcore.SourceSemantics.Internal.Compiled.Contracts
import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Selected.Children
import Solcore.SourceSemantics.Internal.Execution.CallGraph
import Solcore.SourceSemantics.Internal.Compiled.PrivateDescent
import Solcore.SourceSemantics.Internal.Privacy.Active

/-!
# Loop headers and builtin calls

An initialized header inside a private block keeps its exact item and enclosing node, and a nested
body receives the generalized initializer scope. Builtin calls and the barrier connection sit at the
same height.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedBarrierConnection
/-! Selected compilation constrains the same original finalized templates
which occur in the declarative generalization barrier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedBarrierConnection
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalFinalization
open CoreLowering.CallableCoercionPreparationSteps (Specialized)

private theorem parameters_keep (parameters : ParameterSubstitution) (type : Ty) :
    type.freeVariables ⊆ (parameters.apply type).freeVariables := by
  intro metavariable occurs
  induction type with
  | «variable» value => exact occurs
  | parameter value | constructor value | error => cases occurs
  | proxy inner ih | comptime inner ih => exact ih occurs
  | application left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_application_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | function left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_function_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | product left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_product_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))
  | mapping left right leftIH rightIH =>
      simp only [ParameterSubstitution.apply, Ty.mem_freeVariables_mapping_iff] at occurs ⊢
      exact occurs.elim (fun member => .inl (leftIH member)) (fun member => .inr (rightIH member))

private theorem predicate_parameters_keep (parameters : ParameterSubstitution) (predicate : ProgramPredicate) :
    TypedTraitResolution.predicateVariables predicate ⊆
      TypedTraitResolution.predicateVariables (ProgramPredicate.applyParameters parameters predicate) := by
  intro metavariable occurs
  apply TypedTraitResolution.mem_predicateVariables_iff.mpr
  rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with subject | ⟨argument, present, occurs⟩
  · exact .inl (parameters_keep parameters _ subject)
  · exact .inr ⟨parameters.apply argument, List.mem_map.mpr ⟨argument, present, rfl⟩,
      parameters_keep parameters argument occurs⟩

private theorem closed_predicate_absent {instantiation : DeclarationInstantiation}
    (closed : SourcePreparedOpenCallEdges.InstantiationClosed instantiation = true)
    {predicate : ProgramPredicate} (present : predicate ∈ instantiation.predicates)
    {metavariable : TypeVarId}
    (occurs : metavariable ∈ TypedTraitResolution.predicateVariables predicate) : False := by
  simp only [SourcePreparedOpenCallEdges.InstantiationClosed, Bool.and_eq_true] at closed
  have checked := List.all_eq_true.mp closed.2 predicate present
  simp only [Bool.and_eq_true] at checked
  rcases TypedTraitResolution.mem_predicateVariables_iff.mp occurs with subject | ⟨argument, member, inside⟩
  · rw [List.isEmpty_iff.mp checked.1] at subject
    cases subject
  · rw [List.isEmpty_iff.mp (List.all_eq_true.mp checked.2 argument member)] at inside
    cases inside

/-- A successful selected compilation confines each original finalized
template predicate to its complete owner's quantified variables. The closed
call case uses the same issued ledger predicate; the open case uses the same
discovered instance and checked qualified-read metadata. -/
theorem original_template_scoped {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : Specialized} (member : row ∈ compiled.plan.specializations) {fuel : Nat}
    (selected : Selected compiled row fuel)
    {owner : LocalSchemeTemplateOwner}
    (contains : ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner) :
    ∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
      metavariable ∈ owner.binder.scheme.quantified := by
  have template := sourceLocalSchemeTemplateIds_mem_iff.mpr ⟨owner, contains, rfl⟩
  obtain ⟨solved, solvedMember, same, emitter⟩ :=
    SourceCompiledDirectCallPredicateOrigins.BodyReceipt.finalized_template_emitter selected.body template
  have scopedRow := selected.body.resources.ledger.template_scoped solvedMember (same ▸ template)
  obtain ⟨actualOwner, occurrence, actualContains, actualId, predicateEq, _⟩ := scopedRow.exact_owner
  have ownerEq := selected.body.resources.ledger.templateOwnership.owner_unique
    contains actualContains (same.symm.trans actualId)
  subst actualOwner
  have specializedEmitter :=
    SourceCompiledDirectCallPredicateOrigins.specialized_call emitter row.parameterSubstitution
  rw [← selected.source] at specializedEmitter
  obtain ⟨node, present, callee, arguments, instantiation, form, issued, cataloged, paired⟩ := specializedEmitter
  let specialized := StructuralSubstitution.applyLocalSchemeTemplateOwner row.parameterSubstitution owner
  have specializedContains : ContainsLocalSchemeTemplate row.function.typedBody specialized := by
    rw [selected.source]
    exact StructuralSubstitution.ContainsLocalSchemeTemplate.applyParameters row.parameterSubstitution contains
  intro metavariable occurs
  have specializedOccurs := predicate_parameters_keep row.parameterSubstitution owner.requirement.predicate occurs
  cases closed : SourcePreparedOpenCallEdges.InstantiationClosed instantiation with
  | true =>
      apply False.elim
      apply closed_predicate_absent closed paired
      simpa only [predicateEq] using specializedOccurs
  | false =>
      obtain ⟨receipt⟩ := SourceCompiledTemplateCallOwner.open_call_owner accepted member present form cataloged closed
      exact SourceSelectedTemplateInventory.contextual_predicate_scoped
        accepted member form receipt specializedContains issued specializedOccurs

/-- The actual final ledger preserves the same owner and predicate. This
exposes precisely the quantified variables relevant to the generalization
barrier, without replacing the original ledger by the specialized one. -/
theorem original_solved_template_scoped {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : Specialized} (member : row ∈ compiled.plan.specializations) {fuel : Nat}
    (selected : Selected compiled row fuel)
    {solved : SolvedRequirement} (present : solved ∈ selected.body.finalized.solvedRequirements)
    (template : solved.id ∈ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource) :
    ∃ owner, ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner ∧
      solved.id = owner.requirement.templateRequirement ∧
      solved.predicate = owner.requirement.predicate ∧
      (∀ metavariable ∈ TypedTraitResolution.predicateVariables solved.predicate,
        metavariable ∈ owner.binder.scheme.quantified) := by
  obtain ⟨owner, occurrence, contains, same, predicateEq, _⟩ :=
    (selected.body.resources.ledger.template_scoped present template).exact_owner
  refine ⟨owner, contains, same, predicateEq, ?_⟩
  rw [predicateEq]
  exact original_template_scoped accepted member selected contains

end Solcore.SourceSemantics.SourceCompiledGeneralizedBarrierConnection
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedBuiltinCall
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem builtinCall_typing_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel parentFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ∀ smaller, smaller < childFuel → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {expected : Option Ty} {parentInitial initial argumentState resultState : State}
    {inferred : InferredExpression} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {function : BuiltinFunctionId} {call : ExpressionId}
    (boundary : RetainedExpressionBoundary selected parentFuel inferenceContext expression expected
      parentInitial inferred resultState frames target)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (argumentsHere : callProvenance (.expressions childFuel inferenceContext argumentSources initial arguments argumentState))
    (argumentsSuccess : Detail.inferExprsFuel childFuel inferenceContext argumentSources initial =
      .ok (arguments, argumentState))
    (recording : Detail.recordBuiltinFunctionCall expression callee name function arguments
      call expected argumentState = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  let roots := bodyRoots selected
  let evidenceState := selected.body.returned
  have resources := selected.body.resources
  have interfaces := boundary.interfaces
  have resultSubstitutionExtension := boundary.extension
  have ownerEq := boundary.scope.owner
  have typeParametersEq := boundary.scope.parameters
  have signatureFormation := boundary.scope.formation checked
  have functionsCanonical := boundary.scope.functionsCanonical checked
  have canonical := boundary.scope.canonical checked
  have actual := boundary.actual
  have semanticPreserved := boundary.proper
  have rawProper := boundary.rawProper
  have integerPatternsSubset := boundary.integerPatterns
  have integerLiteralsSubset := boundary.integerLiterals
  have requirementsSubset := boundary.requirements
  have covered := boundary.covered
  have actualCovered := boundary.actualCovered
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
    fun type member => (expectedBelow type member).weaken argumentProperties.1.next_le
  have recordProperties := Detail.recordBuiltinFunctionCall_inferenceProperties
    argumentProperties.2.1 argumentProperties.2.2 expectedAtArguments recording
  have argumentExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have metadata := recordBuiltinFunctionCall_metadata recording
  obtain ⟨calleeId, nodesEq⟩ := Detail.recordBuiltinFunctionCall_success_nodes recording
  have argumentToParent : TypingSourceExtends (argumentState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    refine ⟨metadata.1, ?_⟩
    change argumentState.nodes <+: resultState.nodes
    rw [nodesEq]
    exact List.prefix_append _ _
  let callNode : ExpressionNode := {
    id := inferred.id
    span := expression.span
    type := inferred.type
    form := .call calleeId (arguments.map (·.id)) (.builtinFunction function)
  }
  have callContains : ContainsExpression (resultState.toTypedSource roots) inferred.id callNode := by
    refine ⟨?_, rfl⟩
    change .expression callNode ∈ resultState.nodes
    rw [nodesEq]
    simp [callNode]
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [callNode, nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have argumentPatterns : argumentState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← metadata.2.1]
    exact integerPatternsSubset
  have argumentLiterals : argumentState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← metadata.2.2]
    exact integerLiteralsSubset
  have argumentRequirements := List.Subset.trans
    (Detail.recordBuiltinFunctionCall_requirements_subset recording) requirementsSubset
  have argumentsTyped := expressionsRooted_for checked descend childFuel recursive
    argumentsHere argumentsSuccess interfaces argumentExtension boundary.scope invariant actual operational
    (fun argument member => (rawProper.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    argumentPatterns argumentLiterals argumentRequirements
    (fun argument member => covered.expressionChild resources.graph_closed (boundary.directChildren (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (boundary.directChildren (argumentEdge argument member)))
  exact recordBuiltinFunctionCall_expressionTypingBase_actual recording resultSubstitutionExtension
    semanticPreserved argumentsTyped
    (invariant.typeParameterBinders (by simpa only [ownerEq, typeParametersEq] using canonical))


theorem builtinCall_typing
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel parentFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {expected : Option Ty} {parentInitial initial argumentState resultState : State}
    {inferred : InferredExpression} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {function : BuiltinFunctionId} {call : ExpressionId}
    (boundary : RetainedExpressionBoundary selected parentFuel inferenceContext expression expected
      parentInitial inferred resultState frames target)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (argumentsSuccess : Detail.inferExprsFuel childFuel inferenceContext argumentSources initial =
      .ok (arguments, argumentState))
    (recording : Detail.recordBuiltinFunctionCall expression callee name function arguments
      call expected argumentState = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact builtinCall_typing_for (callProvenance := fun _ => True) checked true_childClosed
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary)
    boundary invariant operational expectedBelow True.intro argumentsSuccess recording

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledGeneralizedHeaderInitializer
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness ProtectedVariables SourceInferenceExecution

private theorem annotation_admissible
    {inferenceContext : SourceInference.Context} {target : SourceSemantics.Context}
    {annotation : Option Syntax.TypeExpr} {expected : Option Ty} {outer : Substitution}
    (canonical : SignatureParametersWellFormed inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures : target.signatures = inferenceContext.signatures)
    (parameters : target.typeParameters = inferenceContext.typeParameters)
    (owner : target.currentDeclaration = some inferenceContext.scope.genericOwner)
    (accepted : SourceInference.LocalLetRequirementTiming.Annotation inferenceContext annotation expected) :
    ∀ type ∈ expected, TypeAdmissible target (outer.apply type) := by
  cases accepted with
  | none => simp
  | some resolved =>
    intro type present
    cases Option.mem_def.mp present
    rw [Detail.resolveSourceType_success_apply_eq_self _ resolved]
    exact TypeAdmissible.ofWellFormed
      (resolveSourceType_success_typeWellFormed canonical signatures parameters owner resolved)

/-- The only remaining generalization premise concerns this exact header
allocation. Its child, source ownership and final predicates are produced by
actual inference and the selected finalizer. -/
theorem forItem_initialized_of_receipt_for {provenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed provenance)
    (childSound : ExpressionRootedSoundnessFor provenance selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : provenance (.forItem (childFuel + 1) inferenceContext item initial inferred final))
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target)
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel inferenceContext item initial (inferred, final))
    (barrier : GeneralizationBarrierTransport receipt.ready receipt.locals initial.nextRequirement
      (receipt.ready.resolve receipt.value.type) selected.body.finalized.substitution target
      (localSchemeTemplateIds (receipt.binding.1.applySubstitution selected.body.finalized.substitution))) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  have itemEq : inferred = .letDecl receipt.binding.1 (some receipt.value.id) := receipt.recorded
  have properties := receipt.initializer_inference boundary.invariant.ready formation canonical
  have extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    have atResult := boundary.extension
    rw [receipt.inference_eq] at atResult
    exact atResult
  have priorAvoided := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.value_avoids_active receipt
    boundary.invariant.ready boundary.operational.requirements boundary.operational.quantifiersBelow
    boundary.operational.privacy catalog formation canonical
  let binding : InitializedLetBinding := ⟨receipt.binding.1, .expression receipt.value.id⟩
  let closed : InitializedLetBinding := ⟨receipt.binding.1.applySubstitution selected.body.finalized.substitution,
    .expression receipt.value.id⟩
  have bindingMember : binding ∈ forItemInitializedLetBindings inferred := by
    rw [itemEq]
    exact List.mem_singleton_self _
  have retained := boundary.bindingsRetained binding bindingMember
  have noCapture := selected.body.resources.local_no_capture receipt.binding.1 retained.1
  have finalBody : closed.binder.scheme.body = selected.body.finalized.substitution.apply receipt.value.type := by
    have restriction : selected.body.finalized.substitution.without receipt.binding.1.scheme.quantified =
        selected.body.finalized.substitution :=
      FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain _ _ noCapture.quantified_fresh
    have body : receipt.binding.1.scheme.body = receipt.ready.resolve receipt.value.type := by
      change receipt.generalized.scheme.body = _
      exact Detail.generalizeValue_scheme_body _ _ _ _
    change (receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme.body = _
    rw [FlexibleSubstitution.applyTypedBinder_scheme]
    change (selected.body.finalized.substitution.without receipt.binding.1.scheme.quantified).apply
      receipt.binding.1.scheme.body = _
    rw [restriction, body]
    exact extension receipt.value.type
  have childInvariant := (RecursiveExpressionInvariant.ofStatement boundary.invariant).generalizedInitializer closed.binder
  have nested := boundary.actualBindings binding bindingMember
  have childActual := boundary.actual.initializer closed nested.1 nested.2
  have reference : (.expression receipt.value.id : NodeId) ∈ inferred.references := by
    simp [itemEq, ForItemForm.references]
  have childCovered : ActualContext.Covers selected.body.finalized (frames ++ [closed]) (.expression receipt.value.id) :=
    (boundary.actualCovered _ reference).push (.inl rfl)
  have childSource : TypingSourceExtends (receipt.ready.toTypedSource (bodyRoots selected))
      (final.toTypedSource (bodyRoots selected)) := by
    have nodes : final.nodes = receipt.ready.nodes := congrArg (fun p : ForItemForm × State => p.2.nodes) receipt.completed
    refine ⟨congrArg (fun p : ForItemForm × State => p.2.owner) receipt.completed, ?_⟩
    change receipt.ready.nodes <+: final.nodes
    simpa only [nodes] using List.prefix_refl receipt.ready.nodes
  have patternEq : final.integerPatterns = receipt.ready.integerPatterns :=
    congrArg (fun p : ForItemForm × State => p.2.integerPatterns) receipt.completed
  have literalEq : final.integerLiterals = receipt.ready.integerLiterals :=
    congrArg (fun p : ForItemForm × State => p.2.integerLiterals) receipt.completed
  have requirementEq : final.requirements = receipt.ready.requirements :=
    congrArg (fun p : ForItemForm × State => p.2.requirements) receipt.completed
  have childHere := descend here (header_initializer_child receipt boundary.accepted)
  have childTyping := childSound childHere ({
    accepted := receipt.child, interfaces := boundary.interfaces, extension := extension, scope := boundary.scope
    invariant := childInvariant, actual := childActual, operational := boundary.operational
    expectedBelow := receipt.annotationAccepted.variablesBelow _
    expectedAdmissible := annotation_admissible (boundary.scope.canonical checked)
      (childInvariant.signatures_eq_whole.trans boundary.scope.signatures.symm)
      (childInvariant.typeParametersEq.trans boundary.scope.parameters.symm)
      (childInvariant.declarationEq.trans (congrArg some boundary.scope.owner.symm)) receipt.annotationAccepted
    expectedSafe := by
      intro binder member type present
      exact safe_closed _ _ (receipt.annotationAccepted.variablesBelow 0 type present)
    rawSubtree := (boundary.rawReferences _ reference).monoBefore childSource
    integerPatterns := by simpa only [patternEq] using boundary.integerPatterns
    integerLiterals := by simpa only [literalEq] using boundary.integerLiterals
    requirements := by simpa only [requirementEq] using boundary.requirements
    covered := by
      have covered := boundary.covered _ reference
      simpa only [itemEq, forItemCoverageContext, closed] using covered
    actualCovered := childCovered } : RootedExpressionBoundary selected childFuel inferenceContext
      receipt.initializer receipt.expected initial receipt.value receipt.ready (frames ++ [closed])
      (localSchemeInitializerContext target closed.binder))
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have owner : target.currentDeclaration = some selected.signature.id := by
    simpa only [checkingContext, context, ProgramTypeScope.ofDeclaration, declarationEq] using boundary.invariant.declarationEq
  have finalPredicates := selected.originalBindingPredicates checked
    (RecursiveExpressionInvariant.ofStatement boundary.invariant).signatures_eq_whole
    boundary.invariant.typeParametersEq owner boundary.invariant.residual retained.2
  have certificate : UnannotatedInitializedLetCertificate (evidenceSource selected) target
      selected.body.finalized.substitution receipt.binding.1 receipt.value.id := by
    apply unannotatedInitializedLetCertificate_of_finalBarrier_retained selected.body.resources
      (source := evidenceSource selected) (state := receipt.ready) (final := receipt.binding.2)
      (name := receipt.name) (generalized := receipt.generalized)
      rfl rfl rfl boundary.invariant.signaturesEq boundary.invariant.assumptionsMono
      boundary.invariant.solvedRequirementsEq retained.1 retained.2 barrier finalPredicates
      (priorQuantifiersBlockedAt_of_activeQuantifiersAvoided boundary.invariant.active.aligned priorAvoided)
    rw [← selected.body.resources.source_eq]
    change ExpressionHasType selected.body.finalized.typedSource
      (localSchemeInitializerContext target closed.binder) receipt.value.id closed.binder.scheme.body
    rw [finalBody]
    exact childTyping
  have readyActive := boundary.invariant.active.inferExprFuel receipt.child
  have readyBelow := Detail.inferExprFuel_preserves_localBindersBelowNextLocal boundary.invariant.bindersBelow receipt.child
  have sourceOwner : (evidenceSource selected).owner = receipt.ready.owner := by
    have evidenceOwner : (evidenceSource selected).owner = initial.owner := by
      have sourceEq : (evidenceSource selected).owner = selected.body.finalized.typedSource.owner := by
        rw [selected.body.resources.source_eq]
        rfl
      exact sourceEq.trans boundary.owner
    exact evidenceOwner.trans (Detail.inferExprFuel_preserves_owner receipt.child).symm
  obtain ⟨finalContext, active, typing⟩ := unannotatedInitializedForItemHasType_afterSubstitution
    (control := {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth})
    (source := evidenceSource selected) (name := receipt.name)
    (requirementStart := initial.nextRequirement) (generalized := receipt.generalized) rfl rfl
    readyActive readyBelow sourceOwner certificate
  have finalEq : final = receipt.binding.2 := congrArg Prod.snd receipt.completed
  have finalTyping : ForItemHasType selected.body.finalized.typedSource
      {returnType := selected.body.finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth}
      target (inferred.applySubstitution selected.body.finalized.substitution) finalContext := by
    rw [itemEq]
    rw [← selected.body.resources.source_eq] at typing
    exact typing
  have finalActive : ActiveLocalContextInvariant final selected.body.finalized.substitution finalContext := by
    rw [finalEq]
    exact active
  have allRetained : inferred.initializedLetBinders ⊆ (evidenceSource selected).initializedLetBinders := by
    rw [itemEq]
    intro binder member
    have same : binder = receipt.binding.1 := List.mem_singleton.mp member
    exact same ▸ retained.1
  have operational := boundary.operational.ofRetainedHeader selected.body.resources boundary.invariant.ready
    catalog formation canonical allRetained boundary.extension boundary.accepted
  have isolation := SourceInferenceSoundness.LocalHeaderRequirementTiming.Receipt.schemeIsolation receipt properties.2.1
    priorAvoided boundary.invariant.schemeIsolation operational.privacy
  have finalInvariant := RecursiveStatementInvariant.of_forItem_typing boundary.invariant boundary.accepted
    formation canonical finalActive isolation boundary.extension finalTyping
  exact ⟨finalContext, finalInvariant, boundary.actual.of_forItem finalTyping, operational, finalTyping⟩

theorem forItem_initialized_of_receipt
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (childSound : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target)
    (receipt : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel inferenceContext item initial (inferred, final))
    (barrier : GeneralizationBarrierTransport receipt.ready receipt.locals initial.nextRequirement
      (receipt.ready.resolve receipt.value.type) selected.body.finalized.substitution target
      (localSchemeTemplateIds (receipt.binding.1.applySubstitution selected.body.finalized.substitution))) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  exact forItem_initialized_of_receipt_for (provenance := fun _ => True) checked true_childClosed
    (fun _ boundary => childSound boundary) True.intro boundary receipt barrier

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledPrivateForHeaderPrivacy
/-! An initialized header reached inside a private block keeps its exact item
and enclosing for node, together with privacy through the selected finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

/-- An exact returned header item occurs in a retained, real for statement. -/
def RetainedHeaderItem (whole : TypedSource) (item : ForItemForm) : Prop :=
  ∃ original : StatementNode, ∃ initializers test post body,
    .statement original ∈ whole.nodes ∧ original.form = .forLoop initializers test post body ∧
      item ∈ initializers ++ post

structure InitializedHeaderReceiptPrivate
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    {childFuel : Nat} {inferenceContext : SourceInference.Context} {source : Syntax.ForItem}
    {entry : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel inferenceContext source entry result) : Prop where
  ready : receipt.ready.InferenceReady
  extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution
  retained : receipt.binding.1 ∈
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders
  recorded : RetainedHeaderItem
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
    (.letDecl receipt.binding.1 (some receipt.value.id))
  origins : ActiveBinderCaptureOrigins receipt.ready
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
  templates : ∀ older ∈ receipt.ready.localBinders, BinderTemplatesBefore receipt.ready entry.nextRequirement older
  priorAvoided : Avoids (activeSchemeQuantifiers entry) (receipt.ready.resolve receipt.value.type)
  transport : ∀ type, Safe receipt.binding.1.scheme.quantified receipt.ready type →
    Avoids receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)
  newRows : ∀ requirement ∈ selected.body.body.state.requirements, requirement ∉ receipt.ready.requirements →
    ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
      Avoids receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)

private theorem RetainedHeaderItem.initialized
    {whole : TypedSource} {binder : TypedBinder} {value : ExpressionId}
    (retained : RetainedHeaderItem whole (.letDecl binder (some value))) :
    binder ∈ whole.initializedLetBinders := by
  obtain ⟨original,initializers,test,post,body,present,form,item⟩ := retained
  unfold TypedSource.initializedLetBinders
  refine List.mem_flatMap.mpr ⟨_,present,?_⟩
  change binder ∈ original.form.initializedLetBinders
  rw [form]
  rcases List.mem_append.mp item with left | right
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_,left,List.mem_singleton_self _⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_,right,List.mem_singleton_self _⟩)

private theorem initialized_header_of_occurrence
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {headerFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {forms : List ForItemForm}
    (occurrence : HeaderPrivacyOccurrence headerFuel context source initial final selected.body.returned
      (selected.body.body.statements.map NodeId.statement) forms)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes))
    (continuation : final.InferenceProgress selected.body.body.state)
    (itemsRetained : ∀ item ∈ forms, RetainedHeaderItem
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) item)
    (privacy : ∀ protectedVars,
      (∀ q ∈ protectedVars, q.index < final.inference.next) → LiveBindersSafe protectedVars final →
      SafeTransport protectedVars final selected.body.body.state ∧ LiveBindersSafe protectedVars selected.body.body.state ∧
        ∀ row ∈ selected.body.body.state.requirements, row ∉ final.requirements →
          PredicateSafe protectedVars selected.body.body.state row.predicate)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel, ∃ receipt : LocalHeaderRequirementTiming.Receipt childFuel context source occurrence.entry occurrence.result,
      InitializedHeaderReceiptPrivate selected receipt := by
  obtain ⟨childFuel,receipt,ready,_,member⟩ := occurrence.toOccurrence.initialized form formation canonical
  have retainedItem := itemsRetained _ member
  have retainedBinder := retainedItem.initialized
  have resultExtension := Substitution.SemanticallyExtends.trans (selected.inferenceProgress checked).final_substitution
    (occurrence.continuation.trans continuation).substitution_extends
  have readyExtension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at resultExtension
  have live := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.active_privacy selected.body.resources receipt
    occurrence.ready occurrence.entryWellFormed formation canonical occurrence.entryActive.backed occurrence.entryActive.origins
    retainedBinder resultExtension
  have properties := receipt.initializer_inference occurrence.ready formation canonical
  have bound : ∀ q ∈ receipt.binding.1.scheme.quantified, q.index < occurrence.result.2.inference.next := by
    intro q member
    have below := properties.2.1.solved.variablesBelow_apply properties.2.2
    have actual := below q (List.mem_filter.mp member).1
    rwa [receipt.inference_eq]
  have withinHeader := occurrence.privacy _ bound live
  have afterwards := privacy _
    (fun q member => Nat.lt_of_lt_of_le (bound q member) occurrence.continuation.next_le) withinHeader.2.1
  have transport := withinHeader.1.trans afterwards.1
  have newRows := new_requirements_trans withinHeader.2.2 afterwards.2.2 afterwards.1
  refine ⟨childFuel,receipt,{
    ready := ready, extension := readyExtension, retained := retainedBinder, recorded := retainedItem,
    origins := occurrence.entryActive.origins.congr_localBinders receipt.ready_binders,
    templates := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.templates_before receipt
      occurrence.entryActive.backed occurrence.ready occurrence.entryWellFormed formation canonical,
    priorAvoided := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.value_avoids_active receipt
      occurrence.ready occurrence.entryWellFormed occurrence.entryActive.bound occurrence.entryActive.privateVars
      catalog formation canonical,
    transport := ?_, newRows := ?_ }⟩
  · intro type safe
    apply selected.finishPrivacy checked _ type
    apply transport type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply selected.finishPrivacy checked _ type
    apply newRows requirement member _ type typeMember
    have same : occurrence.result.2.requirements = receipt.ready.requirements :=
      congrArg (fun result : ForItemForm × State => result.2.requirements) receipt.completed
    simpa only [same] using fresh

namespace PrivateBlockContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

/-- Both header lists are selected by original syntax positions. The returned
context is exactly the entering context, with only loop depth changed for post. -/
theorem initialized_for_header (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {statementIndex : Nat} {statement : Syntax.Statement} (statementPosition : block.sources[statementIndex]? = some statement)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan}
    (statementForm : statement.value = .forLoop headerSpan initializers condition post body)
    (isPost : Bool) {headerIndex : Nat} {source : Syntax.ForItem}
    (position : (if isPost then post else initializers)[headerIndex]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ childFuel entry result, ∃ receipt : LocalHeaderRequirementTiming.Receipt childFuel
      (if isPost then ForStatementInferenceContinuation.loopContext block.inferenceContext else block.inferenceContext)
      source entry result, InitializedHeaderReceiptPrivate selected receipt := by
  obtain ⟨occurrence⟩ := block.position checked statementPosition
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq,Detail.inferStatementFuel] at accepted
  | succ childFuel =>
    rw [fuelEq] at accepted
    obtain ⟨receipt⟩ := ForStatementInferenceContinuation.of_accepted statementForm accepted
    have formation := block.toBlockContinuation.formation checked
    have canonical := block.toBlockContinuation.canonical checked
    have catalog : SignatureCatalogWellFormed block.inferenceContext.signatures :=
      block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
    have parent := occurrence.continuation.trans block.continuation
    have resultExtension := Substitution.SemanticallyExtends.trans (selected.inferenceProgress checked).final_substitution
      parent.substitution_extends
    have resultSource : TypingSourceExtends
        (occurrence.result.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) := {
      owner_eq := block.retainedSource.owner_eq.trans occurrence.resultOwner,
      nodes_prefix := occurrence.retained.trans block.retainedSource.nodes_prefix }
    have active : ActiveHeaderState occurrence.entry
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) :=
      ⟨occurrence.entryPrivate,occurrence.entryBound,occurrence.entryTemplates,occurrence.entryOrigins⟩
    have stages := ProtectedVariables.ForStatementInferenceContinuation.Receipt.active_stages receipt
      selected.body.resources occurrence.ready occurrence.entryWellFormed occurrence.entryNodesBelow catalog formation canonical
      block.expectedClosed active resultSource resultExtension
    have facts := receipt.inference occurrence.ready formation canonical (block.expectedBelow.weaken occurrence.before.next_le)
    have allRetained := ProtectedVariables.ForStatementInferenceContinuation.Receipt.headers_retained (roots := selected.body.body.statements.map NodeId.statement) receipt resultSource.nodes_prefix
    have afterFor := block.after_unchanged_occurrence occurrence rfl (List.Subset.refl _) rfl
    have retainedItems : ∀ item ∈ receipt.initialized.items ++ receipt.postResult.items,
        RetainedHeaderItem (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) item := by
      intro item member
      exact ⟨_,_,_,_,_,resultSource.nodes_prefix.subset receipt.recorded,rfl,member⟩
    cases isPost with
    | false =>
      have continuation := facts.2.2.1.trans parent
      have extension := Substitution.SemanticallyExtends.trans (selected.inferenceProgress checked).final_substitution
        continuation.substitution_extends
      obtain ⟨header⟩ := headerPrivacyOccurrence_of_position
        (initial := occurrence.entry.allocateStatementId.2) (show ActiveHeaderState occurrence.entry.allocateStatementId.2
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) from
            ⟨active.privateVars.congr rfl rfl,active.bound,active.backed.congr rfl rfl rfl,active.origins.congr_localBinders rfl⟩)
        selected.body.resources facts.1 occurrence.entryWellFormed
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow)
        catalog formation canonical
        (fun _ member => allRetained (List.mem_append_left _ member)) extension receipt.initialization position
      obtain ⟨headerFuel,headerReceipt,privateReceipt⟩ := initialized_header_of_occurrence checked header catalog formation canonical
        continuation (fun _ member => retainedItems _ (List.mem_append_left _ member)) (by
          intro protectedVars bound live
          have withinFor := ProtectedVariables.ForStatementInferenceContinuation.Receipt.privacy_after_initialization receipt
            occurrence.ready occurrence.entryWellFormed catalog formation canonical block.expectedClosed bound live
          have outer := afterFor protectedVars
            (fun q member => Nat.lt_of_lt_of_le (bound q member) facts.2.2.1.next_le) withinFor.2.1
          exact ⟨withinFor.1.trans outer.1,outer.2.1,new_requirements_trans withinFor.2.2 outer.2.2 outer.1⟩) form
      exact ⟨headerFuel,header.entry,header.result,headerReceipt,privateReceipt⟩
    | true =>
      have initProperties := Detail.inferForItemsFuel_inferenceProperties occurrence.ready.allocateStatementId formation canonical receipt.initialization
      have initBelow := (Detail.inferForItemsFuel_occurrenceBoundExtends receipt.initialization).nodesBelowNextOccurrence
        (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow)
      have initWellFormed := (Detail.inferForItemsFuel_direct_progress receipt.initialization).wellFormed occurrence.entryWellFormed
      have testProperties := Detail.inferExprFuel_inferenceProperties initProperties.2 formation canonical
        (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) receipt.tested
      have testBelow := (Detail.inferExprFuel_occurrenceBoundExtends receipt.tested).nodesBelowNextOccurrence initBelow
      have testWellFormed := (Detail.inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed
      have bodyBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends receipt.bodyAccepted).nodesBelowNextOccurrence testBelow
      have bodyWellFormed := (Detail.inferStatementsFuel_direct_progress receipt.bodyAccepted).wellFormed testWellFormed
      have continuation := facts.2.2.2.trans parent
      have extension := Substitution.SemanticallyExtends.trans (selected.inferenceProgress checked).final_substitution
        continuation.substitution_extends
      obtain ⟨header⟩ := headerPrivacyOccurrence_of_position
        (context := ForStatementInferenceContinuation.loopContext block.inferenceContext)
        stages.2 selected.body.resources facts.2.1 bodyWellFormed bodyBelow catalog formation canonical
        (fun _ member => allRetained (List.mem_append_right _ member)) extension receipt.postAccepted position
      obtain ⟨headerFuel,headerReceipt,privateReceipt⟩ := initialized_header_of_occurrence checked header catalog formation canonical
        continuation (fun _ member => retainedItems _ (List.mem_append_right _ member)) (by
          intro protectedVars bound live
          have withinFor := ProtectedVariables.ForStatementInferenceContinuation.Receipt.privacy_after_post receipt live
          have outer := afterFor protectedVars
            (fun q member => Nat.lt_of_lt_of_le (bound q member) facts.2.2.2.next_le) withinFor.2.1
          exact ⟨withinFor.1.trans outer.1,outer.2.1,new_requirements_trans withinFor.2.2 outer.2.2 outer.1⟩) form
      exact ⟨headerFuel,header.entry,header.result,headerReceipt,privateReceipt⟩

end PrivateBlockContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledPrivateForBodyDescent
/-! A nested for body receives the actual generalized initializer scope. Its
continuation follows post inference and both real saved-scope restorations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat} {selected : BodySelection compiled row fuel}

theorem enter_for_body (block : PrivateBlockContinuation selected)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement} (position : block.sources[index]? = some source)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan}
    (form : source.value = .forLoop headerSpan initializers condition post body) :
    ∃ child : PrivateBlockContinuation selected, child.sources = body.value ∧
      child.inferenceContext = ForStatementInferenceContinuation.loopContext block.inferenceContext := by
  obtain ⟨occurrence⟩ := block.position checked position
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq,Detail.inferStatementFuel] at accepted
  | succ childFuel =>
    rw [fuelEq] at accepted
    obtain ⟨receipt⟩ := ForStatementInferenceContinuation.of_accepted form accepted
    have formation := block.toBlockContinuation.formation checked
    have canonical := block.toBlockContinuation.canonical checked
    have catalog : SignatureCatalogWellFormed block.inferenceContext.signatures :=
      block.signatures.symm ▸ SignatureCatalogWellFormed.ofCheckProgram checked
    have parent := occurrence.continuation.trans block.continuation
    have resultExtension := Substitution.SemanticallyExtends.trans (selected.inferenceProgress checked).final_substitution
      parent.substitution_extends
    have resultSource : TypingSourceExtends
        (occurrence.result.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) := {
      owner_eq := block.retainedSource.owner_eq.trans occurrence.resultOwner,
      nodes_prefix := occurrence.retained.trans block.retainedSource.nodes_prefix }
    have active : ActiveHeaderState occurrence.entry
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) :=
      ⟨occurrence.entryPrivate,occurrence.entryBound,occurrence.entryTemplates,occurrence.entryOrigins⟩
    have stages := ProtectedVariables.ForStatementInferenceContinuation.Receipt.active_stages receipt
      selected.body.resources occurrence.ready occurrence.entryWellFormed occurrence.entryNodesBelow catalog formation canonical
      block.expectedClosed active resultSource resultExtension
    have initProperties := Detail.inferForItemsFuel_inferenceProperties occurrence.ready.allocateStatementId formation canonical receipt.initialization
    have initWellFormed := (Detail.inferForItemsFuel_direct_progress receipt.initialization).wellFormed occurrence.entryWellFormed
    have initBelow := (Detail.inferForItemsFuel_occurrenceBoundExtends receipt.initialization).nodesBelowNextOccurrence
      (State.allocateStatementId_preserves_nodesBelowNextOccurrence occurrence.entry occurrence.entryNodesBelow)
    have boolClosed : ∀ type ∈ some Ty.bool, type.VariablesBelow 0 := by
      intro type member
      cases Option.mem_def.mp member
      exact Ty.variablesBelow_constructor _ _
    have testProperties := Detail.inferExprFuel_inferenceProperties initProperties.2 formation canonical
      (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested
    have testBelow := (Detail.inferExprFuel_occurrenceBoundExtends receipt.tested).nodesBelowNextOccurrence initBelow
    have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
      (context := ForStatementInferenceContinuation.loopContext block.inferenceContext)
      testProperties.2.1 formation canonical (block.expectedClosed.weaken (Nat.zero_le _)) receipt.bodyAccepted
    have bodyBelow := (Detail.inferStatementsFuel_occurrenceBoundExtends receipt.bodyAccepted).nodesBelowNextOccurrence testBelow
    have restored := State.restoreLexicalScope_inferenceProperties initProperties.2 (testProperties.1.trans bodyProperties.1)
    have postProperties := Detail.inferForItemsFuel_inferenceProperties
      (context := ForStatementInferenceContinuation.loopContext block.inferenceContext)
      restored.2 formation canonical receipt.postAccepted
    have last := State.InferenceProgress.of_inference_eq postProperties.2.solved receipt.inference_eq
    have bodyContinuation := (State.InferenceProgress.restoreLexicalScope receipt.bodyResult.state
      receipt.initialized.state.lexicalScope bodyProperties.2.1.solved).trans (postProperties.1.trans last)
    have bodyNodes : receipt.bodyResult.state.nodes <+: occurrence.result.state.nodes := by
      have beforePost := Detail.inferForItemsFuel_preserves_nodesPrefix receipt.postAccepted
        (List.prefix_refl _) bodyBelow (Nat.le_refl _)
      have postNodes : receipt.postResult.state.nodes <+: occurrence.result.state.nodes := by
        rw [congrArg (fun result : Detail.StatementResult => result.state.nodes) receipt.completed]
        exact List.prefix_append _ _
      exact beforePost.trans postNodes
    have bodySource : TypingSourceExtends
        (receipt.bodyResult.state.toTypedSource (selected.body.body.statements.map NodeId.statement))
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) := {
      owner_eq := resultSource.owner_eq.trans ((congrArg (fun result : Detail.StatementResult => result.state.owner)
        receipt.completed).trans (Detail.inferForItemsFuel_preserves_owner
          (state := receipt.bodyResult.state.restoreLexicalScope receipt.initialized.state.lexicalScope) receipt.postAccepted)),
      nodes_prefix := bodyNodes.trans resultSource.nodes_prefix }
    have afterFor := block.after_unchanged_occurrence occurrence rfl (List.Subset.refl _) rfl
    refine ⟨{
      checkingFuel := childFuel, inferenceContext := ForStatementInferenceContinuation.loopContext block.inferenceContext,
      sources := body.value, expected := block.expected, entry := receipt.testState, result := receipt.bodyResult,
      signatures := block.signatures, accepted := receipt.bodyAccepted, ready := testProperties.2.1,
      nodesBelow := testBelow, expectedBelow := block.expectedClosed.weaken (Nat.zero_le _),
      continuation := bodyContinuation.trans parent,
      retained := bodyNodes.trans (occurrence.retained.trans block.retained),
      entryWellFormed := (Detail.inferExprFuel_direct_progress receipt.tested).wellFormed initWellFormed,
      entryTemplates := stages.1.backed.inferExprFuel initProperties.2 formation canonical
        (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested,
      entryOrigins := stages.1.origins.inferExprFuel receipt.tested,
      entryPrivate := stages.1.privateVars.inferExprFuel initProperties.2 initWellFormed stages.1.bound catalog
        formation canonical boolClosed receipt.tested,
      entryBound := activeQuantifiersBelowNext_inferExprFuel stages.1.bound initProperties.2 formation canonical
        (fun type member => (boolClosed type member).weaken (Nat.zero_le _)) receipt.tested,
      expectedClosed := block.expectedClosed, retainedSource := bodySource, privacy := ?_
    },rfl,rfl⟩
    intro protectedVars bound live
    have withinFor := ProtectedVariables.ForStatementInferenceContinuation.Receipt.privacy_after_body receipt
      occurrence.ready occurrence.entryWellFormed catalog formation canonical block.expectedClosed bound live
    have outer := afterFor protectedVars
      (fun q member => Nat.lt_of_lt_of_le (bound q member) bodyContinuation.next_le) withinFor.2.1
    exact ⟨withinFor.1.trans outer.1,outer.2.1,new_requirements_trans withinFor.2.2 outer.2.2 outer.1⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.PrivateBlockContinuation
end
