import Solcore.SourceSemantics.SourceInferenceStatementAssignmentSoundness

/-!
The declarative indexing rule for an actual, fully exposed place-inference
trace.  The recursive place and mapping-key judgments are supplied only for
the concrete children of this trace.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- An indexed place is well typed from the two actual child judgments, the
mapping unification, and the frontend's exact resulting place shape. -/
theorem inferPlaceFuel_index_sound_of_actual_typed_children
    {source : TypedSource} {outer : Substitution}
    {target : SourceSemantics.Context}
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {base key : Syntax.Expr}
    {initial baseState keyInitial final : State}
    {basePlace place : PlaceResolution}
    {inferredKey : InferredExpression}
    (_baseSuccess : Detail.inferPlaceFuel fuel inferenceContext base initial =
      .ok (basePlace, baseState))
    (unifySuccess : Detail.unify baseState.fresh.2.fresh.2 basePlace.type
      (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) =
        .ok keyInitial)
    (keySuccess : Detail.inferExprFuel fuel inferenceContext key
      (some (keyInitial.resolve baseState.fresh.1)) keyInitial =
        .ok (inferredKey, final))
    (placeEq : place = { basePlace with
      projections := basePlace.projections ++ [.index inferredKey.id]
      type := final.resolve baseState.fresh.2.fresh.1 })
    (outerUnified : outer.SemanticallyExtends
      keyInitial.inference.substitution)
    (outerFinal : outer.SemanticallyExtends final.inference.substitution)
    (baseTyped : SourcePlaceHasType (source.applySubstitution outer) target
      (basePlace.applySubstitution outer) (outer.apply basePlace.type))
    (keyTyped : ExpressionHasType (source.applySubstitution outer) target
      inferredKey.id (outer.apply inferredKey.type)) :
    SourcePlaceHasType (source.applySubstitution outer) target
      (place.applySubstitution outer) (outer.apply place.type) := by
  have mappingEq : outer.apply basePlace.type =
      .mapping (outer.apply baseState.fresh.1)
        (outer.apply baseState.fresh.2.fresh.1) := by
    calc
      outer.apply basePlace.type =
          outer.apply (keyInitial.resolve basePlace.type) := by
        simpa [State.resolve, TypeSystem.InferState.resolve] using
          (outerUnified basePlace.type).symm
      _ = outer.apply (keyInitial.resolve
            (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)) :=
        congrArg outer.apply (Detail.unify_resolve_eq unifySuccess)
      _ = outer.apply
            (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) := by
        simpa [State.resolve, TypeSystem.InferState.resolve] using
          outerUnified
            (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)
      _ = .mapping (outer.apply baseState.fresh.1)
            (outer.apply baseState.fresh.2.fresh.1) := rfl
  have baseMapping : SourcePlaceHasType (source.applySubstitution outer)
      target (basePlace.applySubstitution outer)
      (.mapping (outer.apply baseState.fresh.1)
        (outer.apply baseState.fresh.2.fresh.1)) := by
    rw [← mappingEq]
    exact baseTyped
  have keyExpectedEq : outer.apply inferredKey.type =
      outer.apply baseState.fresh.1 := by
    calc
      outer.apply inferredKey.type =
          outer.apply (keyInitial.resolve baseState.fresh.1) :=
        Detail.inferExprFuel_expected_type_apply_eq keySuccess outerFinal
      _ = outer.apply baseState.fresh.1 := by
        simpa [State.resolve, TypeSystem.InferState.resolve] using
          outerUnified baseState.fresh.1
  have keyType : ExpressionHasType (source.applySubstitution outer) target
      inferredKey.id (outer.apply baseState.fresh.1) := by
    rw [← keyExpectedEq]
    exact keyTyped
  have indexed := SourcePlaceHasType.snocIndex baseMapping keyType
  have resolvedValueEq :
      outer.apply (final.resolve baseState.fresh.2.fresh.1) =
        outer.apply baseState.fresh.2.fresh.1 := by
    simpa [State.resolve, TypeSystem.InferState.resolve] using
      outerFinal baseState.fresh.2.fresh.1
  subst place
  simpa [PlaceResolution.applySubstitution, resolvedValueEq] using indexed

end Solcore.SourceSemantics.SourceInferenceSoundness
