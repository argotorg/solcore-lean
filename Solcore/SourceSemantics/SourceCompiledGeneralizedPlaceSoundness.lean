import Solcore.SourceSemantics.SourceCompiledGeneralizedPlaceContracts

/-! Writable places and their mapping keys use the same selected final source.
Every recursive key boundary comes from the actual place traversal. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel}

theorem placeRootedSoundness
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ∀ childFuel, (∀ smaller, smaller < childFuel → ExpressionRootedSoundness selected smaller) →
      PlaceRootedSoundness selected childFuel := by
  intro childFuel
  induction childFuel with
  | zero =>
      intro _ inferenceContext expression initial final place frames target boundary
      have success := boundary.accepted
      simp only [Detail.inferPlaceFuel] at success
      cases success
  | succ childFuel induction =>
      intro expressionSound inferenceContext expression initial final place frames target boundary
      have formation := boundary.scope.formation checked
      have canonical := boundary.scope.functionsCanonical checked
      have catalog := boundary.scope.catalog checked
      refine ⟨?_, boundary.operational.ofPlace boundary.invariant.ready catalog formation canonical boundary.accepted,
        boundary.operational.place_type_private boundary.invariant.ready catalog formation canonical boundary.accepted⟩
      cases form : expression.value
      case identifier name =>
        rw [selected.body.resources.source_eq]
        exact inferPlaceFuel_success_identifier_sound form boundary.accepted
          boundary.invariant.active boundary.extension
      case group inner =>
        have childSuccess : Detail.inferPlaceFuel childFuel inferenceContext inner initial = .ok (place, final) := by
          simpa only [Detail.inferPlaceFuel, form] using boundary.accepted
        exact (induction (fun smaller below => expressionSound smaller
          (Nat.lt_trans below (Nat.lt_succ_self childFuel)))
          { boundary with accepted := childSuccess }).1
      case index base brackets key =>
        obtain ⟨basePlace, baseState, keyInitial, inferredKey, baseSuccess,
            baseInvariant, unifySuccess, keySuccess, placeEq, keyInvariant,
            keyExpectedBelow, keyMember⟩ :=
          inferPlaceFuel_index_key_invariant form boundary.accepted formation canonical
            boundary.invariant boundary.extension
        obtain ⟨actualPlace, actualState, actualSuccess, _baseBelow, baseToFinal,
            baseLiterals, basePatterns, baseRequirements⟩ :=
          inferPlaceFuel_success_index_base_state_provenance form boundary.accepted
            boundary.invariant.nodesBelow (bodyRoots selected)
        rw [baseSuccess] at actualSuccess
        obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
        have baseReferences : ∀ keyId, .expression keyId ∈ basePlace.references →
            .expression keyId ∈ place.references := by
          intro keyId member
          exact inferPlaceFuel_index_base_references_subset form baseSuccess boundary.accepted member
        have baseTyped := (induction (fun smaller below => expressionSound smaller
          (Nat.lt_trans below (Nat.lt_succ_self childFuel))) ({
            accepted := baseSuccess
            interfaces := boundary.interfaces
            extension := baseInvariant.substitutionExtension
            scope := boundary.scope
            invariant := boundary.invariant
            actual := boundary.actual
            operational := boundary.operational
            rawKeys := fun keyId member => (boundary.rawKeys keyId (baseReferences keyId member)).monoBefore baseToFinal
            integerPatterns := List.Subset.trans basePatterns boundary.integerPatterns
            integerLiterals := List.Subset.trans baseLiterals boundary.integerLiterals
            requirements := List.Subset.trans baseRequirements boundary.requirements
            covered := fun keyId member => boundary.covered keyId (baseReferences keyId member)
            actualCovered := fun keyId member => boundary.actualCovered keyId (baseReferences keyId member)
          } : PlaceBoundary selected childFuel inferenceContext base initial basePlace baseState frames target)).1
        obtain ⟨keyOperational, keySafe⟩ := boundary.operational.placeIndexPrefix boundary.invariant.ready
          catalog formation canonical baseSuccess unifySuccess
        have baseEq : selected.body.finalized.substitution.apply basePlace.type =
            .mapping (selected.body.finalized.substitution.apply baseState.fresh.1)
              (selected.body.finalized.substitution.apply baseState.fresh.2.fresh.1) := by
          calc
            selected.body.finalized.substitution.apply basePlace.type =
                selected.body.finalized.substitution.apply (keyInitial.resolve basePlace.type) := by
              simpa only [State.resolve, InferState.resolve] using
                (keyInvariant.substitutionExtension basePlace.type).symm
            _ = selected.body.finalized.substitution.apply
                (keyInitial.resolve (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)) :=
              congrArg selected.body.finalized.substitution.apply (Detail.unify_resolve_eq unifySuccess)
            _ = .mapping (selected.body.finalized.substitution.apply baseState.fresh.1)
                  (selected.body.finalized.substitution.apply baseState.fresh.2.fresh.1) := by
              simpa only [State.resolve, InferState.resolve, Substitution.apply] using
                keyInvariant.substitutionExtension (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)
        have expectedEq : selected.body.finalized.substitution.apply (keyInitial.resolve baseState.fresh.1) =
            selected.body.finalized.substitution.apply baseState.fresh.1 := by
          simpa only [State.resolve, InferState.resolve] using keyInvariant.substitutionExtension baseState.fresh.1
        have keyTyped := expressionSound childFuel (Nat.lt_succ_self childFuel) ({
          accepted := keySuccess
          interfaces := boundary.interfaces
          extension := boundary.extension
          scope := boundary.scope
          invariant := keyInvariant
          actual := boundary.actual
          operational := keyOperational
          expectedBelow := by
            intro type member
            have same : type = keyInitial.resolve baseState.fresh.1 := (Option.some.inj member).symm
            subst type
            exact keyExpectedBelow
          expectedAdmissible := by
            intro type member
            have same : type = keyInitial.resolve baseState.fresh.1 := (Option.some.inj member).symm
            subst type
            rw [expectedEq]
            have valid := sourcePlace_type_admissible baseTyped
            rw [baseEq] at valid
            exact TypeAdmissible.mapping_key valid
          expectedSafe := by
            intro binder member type typeMember
            have same : type = keyInitial.resolve baseState.fresh.1 := (Option.some.inj typeMember).symm
            subst type
            exact keySafe binder member
          rawSubtree := boundary.rawKeys inferredKey.id keyMember
          integerPatterns := boundary.integerPatterns
          integerLiterals := boundary.integerLiterals
          requirements := boundary.requirements
          covered := boundary.covered inferredKey.id keyMember
          actualCovered := boundary.actualCovered inferredKey.id keyMember
        } : RootedExpressionBoundary selected childFuel inferenceContext key
          (some (keyInitial.resolve baseState.fresh.1)) keyInitial inferredKey final frames target)
        rw [selected.body.resources.source_eq] at baseTyped keyTyped ⊢
        exact inferPlaceFuel_index_sound_of_actual_typed_children baseSuccess unifySuccess keySuccess placeEq
          keyInvariant.substitutionExtension boundary.extension baseTyped keyTyped
      all_goals
        have success := boundary.accepted
        simp [Detail.inferPlaceFuel, form] at success

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
