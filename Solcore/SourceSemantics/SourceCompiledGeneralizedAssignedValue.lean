import Solcore.SourceSemantics.SourceCompiledGeneralizedPlaceContracts
import Solcore.SourceSemantics.SourceInferenceSelectedAssignmentChildren

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

structure AssignedValueBoundary {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) (childFuel : Nat) (inferenceContext : SourceInference.Context)
    (targetExpression : Syntax.Expr) (operator : Syntax.ValueAssignOp) (value : Syntax.Expr)
    (initial : State) (assignment : AssignmentResolution) (inferred : InferredExpression) (final : State)
    (frames : List InitializedLetBinding) (target : SourceSemantics.Context) : Prop where
  accepted : Detail.inferAssignedValueFuel childFuel inferenceContext targetExpression operator value initial =
    .ok (assignment, inferred, final)
  interfaces : ExecutableCoercionInterfaces.SourceInterfaces (checkingContext selected).signatures
    selected.body.finalized.solvedRequirements selected.body.finalized.typedSource
  extension : selected.body.finalized.substitution.SemanticallyExtends final.inference.substitution
  scope : CheckingScope selected inferenceContext
  invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target
  actual : ActualContext (checkingContext selected) selected.body.finalized frames target
  operational : GeneralizedActualStateInvariant initial (evidenceSource selected)
  rawKeys : ∀ key, .expression key ∈ assignment.references →
    RawSubtreePreserved (final.toTypedSource (bodyRoots selected)) (evidenceSource selected) (.expression key)
  rawValue : RawSubtreePreserved (final.toTypedSource (bodyRoots selected)) (evidenceSource selected) (.expression inferred.id)
  integerPatterns : final.integerPatterns ⊆ selected.body.returned.integerPatterns
  integerLiterals : final.integerLiterals ⊆ selected.body.returned.integerLiterals
  requirements : final.requirements ⊆ selected.body.returned.requirements
  keysCovered : ∀ key, .expression key ∈ assignment.references →
    TemplateScopeCovered selected.body.finalized.typedSource target (.expression key)
  valueCovered : TemplateScopeCovered selected.body.finalized.typedSource target (.expression inferred.id)
  keysActualCovered : ∀ key, .expression key ∈ assignment.references →
    ActualContext.Covers selected.body.finalized frames (.expression key)
  valueActualCovered : ActualContext.Covers selected.body.finalized frames (.expression inferred.id)

theorem assignedValue_of_actual_children
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (placeSound : PlaceRootedSoundness selected childFuel)
    (expressionSound : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {initial final : State}
    {assignment : AssignmentResolution} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : AssignedValueBoundary selected childFuel inferenceContext targetExpression operator value
      initial assignment inferred final frames target) :
    SourceAssignmentHasType selected.body.finalized.typedSource target
      (assignment.applySubstitution selected.body.finalized.substitution) operator inferred.id ∧
    GeneralizedActualStateInvariant final (evidenceSource selected) := by
  have formation := boundary.scope.formation checked
  have canonical := boundary.scope.functionsCanonical checked
  have catalog := boundary.scope.catalog checked
  obtain ⟨place, placeState, expected, valueInitial, placeAccepted, placeInvariant,
      valueAccepted, valueInvariant, expectedBelow, referencesEq, targetEq, valueOrigin⟩ :=
    inferAssignedValueFuel_children_actual_invariants boundary.accepted formation canonical
      boundary.invariant boundary.extension
  obtain ⟨actualPlace, actualPlaceState, actualPlaceAccepted, _, placeToAssignment,
      placeLiterals, placePatterns, placeRequirements⟩ :=
    inferAssignedValueFuel_success_place_state_provenance boundary.accepted boundary.invariant.nodesBelow (bodyRoots selected)
  rw [placeAccepted] at actualPlaceAccepted
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualPlaceAccepted).symm
  have placeReference : ∀ key, .expression key ∈ place.references → .expression key ∈ assignment.references := by
    intro key member
    simpa [AssignmentResolution.references, referencesEq] using member
  obtain ⟨placeTyped, placeOperational, placeSafe⟩ := placeSound ({
    accepted := placeAccepted
    interfaces := boundary.interfaces
    extension := placeInvariant.substitutionExtension
    scope := boundary.scope
    invariant := boundary.invariant
    actual := boundary.actual
    operational := boundary.operational
    rawKeys := fun key member => (boundary.rawKeys key (placeReference key member)).monoBefore placeToAssignment
    integerPatterns := List.Subset.trans placePatterns boundary.integerPatterns
    integerLiterals := List.Subset.trans placeLiterals boundary.integerLiterals
    requirements := List.Subset.trans placeRequirements boundary.requirements
    covered := fun key member => boundary.keysCovered key (placeReference key member)
    actualCovered := fun key member => boundary.keysActualCovered key (placeReference key member) } :
    PlaceBoundary selected childFuel inferenceContext targetExpression initial place placeState frames target)
  have targetTypeEq : selected.body.finalized.substitution.apply assignment.target.type =
      selected.body.finalized.substitution.apply place.type := by
    rw [targetEq]
    simpa [State.resolve, InferState.resolve] using boundary.extension place.type
  have targetSubstEq : assignment.target.applySubstitution selected.body.finalized.substitution =
      place.applySubstitution selected.body.finalized.substitution := by
    rw [targetEq]
    have storedEq : selected.body.finalized.substitution.apply (final.resolve place.type) =
        selected.body.finalized.substitution.apply place.type := by
      simpa [State.resolve, InferState.resolve] using boundary.extension place.type
    simpa [PlaceResolution.applySubstitution] using
      congrArg (fun type => ({ place with type := type } : PlaceResolution)) storedEq
  have placeProperties := Detail.inferPlaceFuel_inferenceProperties boundary.invariant.ready formation canonical placeAccepted
  have valueOperational : GeneralizedActualStateInvariant valueInitial (evidenceSource selected) := by
    rcases valueOrigin with ⟨rfl, _⟩ | ⟨unified, _⟩
    · exact placeOperational
    · exact placeOperational.unify placeProperties.2.1 placeProperties.2.2
        (Ty.variablesBelow_constructor _ _) placeSafe
        (fun binder _ => ProtectedVariables.safe_closed binder.scheme.quantified placeState
          (Ty.variablesBelow_constructor 0 _)) unified
  have expectedSafe : ∀ binder ∈ valueInitial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified valueInitial expected := by
    rcases valueOrigin with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
    · intro binder member
      exact ProtectedVariables.safe_resolved placeProperties.2.1 (placeSafe binder member)
    · intro binder _
      exact ProtectedVariables.safe_closed _ _ (Ty.variablesBelow_constructor 0 _)
  have expectedAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expected) := by
    rcases valueOrigin with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have resolved : selected.body.finalized.substitution.apply (placeState.resolve place.type) =
          selected.body.finalized.substitution.apply place.type := by
        simpa only [State.resolve, InferState.resolve] using placeInvariant.substitutionExtension place.type
      rw [resolved]
      exact sourcePlace_type_admissible placeTyped
    · exact TypeAdmissible.word (boundary.invariant.typeParameterBinders (by
        simpa only [boundary.scope.owner, boundary.scope.parameters] using boundary.scope.canonical checked))
  have expectedBound : ∀ type ∈ some expected, type.VariablesBelow valueInitial.inference.next := by
    intro type member
    have same : type = expected := Option.some.inj member.symm
    simpa only [same] using expectedBelow
  have expectedPrivate : ∀ binder ∈ valueInitial.localBinders, ∀ type ∈ some expected,
      ProtectedVariables.Safe binder.scheme.quantified valueInitial type := by
    intro binder member type present
    have same : type = expected := Option.some.inj present.symm
    simpa only [same] using expectedSafe binder member
  have valueTyped := expressionSound ({
    accepted := valueAccepted
    interfaces := boundary.interfaces
    extension := boundary.extension
    scope := boundary.scope
    invariant := valueInvariant
    actual := boundary.actual
    operational := valueOperational
    expectedBelow := expectedBound
    expectedAdmissible := by
      intro type member
      have same : type = expected := Option.some.inj member.symm
      simpa only [same] using expectedAdmissible
    expectedSafe := expectedPrivate
    rawSubtree := boundary.rawValue
    integerPatterns := boundary.integerPatterns
    integerLiterals := boundary.integerLiterals
    requirements := boundary.requirements
    covered := boundary.valueCovered
    actualCovered := boundary.valueActualCovered } :
    RootedExpressionBoundary selected childFuel inferenceContext value (some expected) valueInitial inferred final frames target)
  have returned := valueOperational.ofExpression valueInvariant.ready catalog formation canonical
    expectedBound expectedPrivate valueAccepted
  refine ⟨?_, returned⟩
  have assignmentPlace : SourcePlaceHasType selected.body.finalized.typedSource target
      (assignment.target.applySubstitution selected.body.finalized.substitution)
      (selected.body.finalized.substitution.apply assignment.target.type) := by
    simpa only [targetSubstEq, targetTypeEq] using placeTyped
  rw [selected.body.resources.source_eq] at assignmentPlace valueTyped ⊢
  exact inferAssignedValueFuel_success_sound_of_typed_result boundary.invariant.ready formation canonical
    boundary.extension assignmentPlace valueTyped boundary.accepted

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
