import Solcore.SourceSemantics.SourceInferenceGeneralizedConstructorState
import Solcore.SourceSemantics.SourceInferenceSelectedPlaceSoundness

/-! Actual place inference preserves the generalized operational state and
keeps the resulting writable type private from active scheme quantifiers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.ofPlace
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {place : PlaceResolution} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferPlaceFuel fuel context expression initial = .ok (place, final)) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferPlaceFuel_inferenceProperties ready formation canonical accepted
  have binders : final.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq accepted)
  refine ⟨⟨pending, (actualLedgerFamily fuel).place accepted ledger⟩,
    invariant.origins.congr_localBinders binders,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.transport (fun _ member => binders ▸ member)
      (Detail.inferPlaceFuel_requirements_subset accepted) properties.1.substitution_extends⟩
  intro binder member
  have old := binders ▸ member
  exact (inferPlaceFuel_private binder.scheme.quantified fuel context expression initial
    ready ledger.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical _ accepted).2.2.1

theorem GeneralizedActualStateInvariant.place_type_private
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {place : PlaceResolution} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferPlaceFuel fuel context expression initial = .ok (place, final)) :
    ∀ binder ∈ final.localBinders, Safe binder.scheme.quantified final place.type := by
  intro binder member
  have binders : final.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq accepted)
  have old := binders ▸ member
  exact (inferPlaceFuel_private binder.scheme.quantified fuel context expression initial
    ready invariant.requirements (invariant.quantifiersBelow binder old) (invariant.privacy binder old)
    catalog formation canonical _ accepted).2.1

theorem GeneralizedActualStateInvariant.placeIndexPrefix
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {initial baseState keyInitial : State} {place : PlaceResolution} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferPlaceFuel fuel context expression initial = .ok (place, baseState))
    (unified : Detail.unify baseState.fresh.2.fresh.2 place.type
      (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) = .ok keyInitial) :
    GeneralizedActualStateInvariant keyInitial source ∧
    ∀ binder ∈ keyInitial.localBinders,
      Safe binder.scheme.quantified keyInitial (keyInitial.resolve baseState.fresh.1) := by
  have properties := Detail.inferPlaceFuel_inferenceProperties ready formation canonical accepted
  have baseOperational := invariant.ofPlace ready catalog formation canonical accepted
  have keyProperties := Detail.fresh_eq_inferenceProperties properties.2.1
    (initial := baseState) (type := baseState.fresh.1) (next := baseState.fresh.2) rfl
  have valueProperties := Detail.fresh_eq_inferenceProperties keyProperties.2.1
    (initial := baseState.fresh.2) (type := baseState.fresh.2.fresh.1)
    (next := baseState.fresh.2.fresh.2) rfl
  have baseBelow := properties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
  have mappingBelow : (Ty.mapping baseState.fresh.1 baseState.fresh.2.fresh.1).VariablesBelow
      baseState.fresh.2.fresh.2.inference.next :=
    (Ty.variablesBelow_mapping_iff _ _ _).2
      ⟨keyProperties.2.2.weaken valueProperties.1.next_le, valueProperties.2.2⟩
  have baseSafe : ∀ binder ∈ baseState.localBinders, Safe binder.scheme.quantified baseState place.type :=
    invariant.place_type_private ready catalog formation canonical accepted
  have freshSafety : ∀ binder ∈ baseState.fresh.2.fresh.2.localBinders,
      Safe binder.scheme.quantified baseState.fresh.2.fresh.2 place.type ∧
      Safe binder.scheme.quantified baseState.fresh.2.fresh.2
        (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) ∧
      Safe binder.scheme.quantified baseState.fresh.2.fresh.2 baseState.fresh.1 := by
    intro binder member
    have baseMember : binder ∈ baseState.localBinders := member
    have keySafe := ProtectedVariables.fresh_type properties.2.1
      (baseOperational.quantifiersBelow binder baseMember)
    have valueSafe := ProtectedVariables.fresh_type keyProperties.2.1
      (baseOperational.fresh.quantifiersBelow binder member)
    have keyAtValue := ProtectedVariables.fresh _ keySafe
    exact ⟨ProtectedVariables.fresh _ (ProtectedVariables.fresh _ (baseSafe binder baseMember)),
      (safe_mapping_iff _ _ _ _).mpr ⟨keyAtValue, valueSafe⟩, keyAtValue⟩
  have operational := baseOperational.fresh.fresh.unify valueProperties.2.1 baseBelow mappingBelow
    (fun binder member => (freshSafety binder member).1)
    (fun binder member => (freshSafety binder member).2.1) unified
  refine ⟨operational, ?_⟩
  intro binder member
  have binders : keyInitial.localBinders = baseState.fresh.2.fresh.2.localBinders :=
    congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified)
  have safety := freshSafety binder (binders ▸ member)
  exact safe_resolved
    (Detail.unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow unified)
    (ProtectedVariables.unify safety.1 safety.2.1 unified _ safety.2.2)

end Solcore.SourceSemantics.SourceInferenceSoundness
