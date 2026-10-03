import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceSignatureFacts

/-! Packed native argument types determine the ordered row only after its
arity is fixed independently. Source binder identity comes from the actual
header agreement. Parameter preparation and its packed signature agreement
remain separate receipts; a native type never authenticates source binders. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedParameterPackingFacts
open Core Frontend SourceInference RecursiveNamedCatalog

/-- Zero and one arguments, or one tuple and several arguments, can have the
same packed type. With equal arity the complete ordered native row is unique. -/
theorem packed_eq_of_length {left right : List Core.Ty}
    (arity : left.length = right.length)
    (packed : SourceCoreCompatibleCatalog.packTypes left =
      SourceCoreCompatibleCatalog.packTypes right) : left = right := by
  induction left generalizing right with
  | nil =>
    have empty : right = [] := List.eq_nil_of_length_eq_zero arity.symm
    exact empty.symm
  | cons head tail ih =>
    cases right with
    | nil => simp at arity
    | cons other rest =>
      have sameLength : tail.length = rest.length := Nat.succ.inj arity
      cases tail with
      | nil =>
        have empty : rest = [] := List.eq_nil_of_length_eq_zero sameLength.symm
        subst rest
        simp only [SourceCoreCompatibleCatalog.packTypes] at packed
        cases packed
        rfl
      | cons next suffix =>
        cases rest with
        | nil => simp at sameLength
        | cons otherNext otherSuffix =>
          simp only [SourceCoreCompatibleCatalog.packTypes] at packed
          have components := Ty.product.inj packed
          have sameHead := components.1
          subst other
          exact congrArg (List.cons head) (ih sameLength components.2)

variable {checked : CallableAncestryPairedLookup.Checked}
  {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The full source parameter agreement supplies arity independently of the
native carrier. The packed agreement is required for the actual prepared row. -/
theorem header_native_types (header : Header prepared values definitions program)
    (parameterPack : header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd)) :
    header.bindings.map Prod.snd = header.named.inputs.map Prod.snd := by
  have binders := header.parameters.symm.trans header.agreement.parameters
  have arity : (header.bindings.map Prod.snd).length =
      (header.named.inputs.map Prod.snd).length := by
    simpa only [List.length_map] using congrArg List.length binders
  exact packed_eq_of_length arity (header.parameterType.symm.trans parameterPack)

/-- Transport real preparation projections along the original ordered source
binders and independently authenticated native row. No source shape or evidence
dictionary is inferred from this native projection receipt. -/
theorem header_projections (header : Header prepared values definitions program)
    (parameterPack : header.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (header.named.inputs.map Prod.snd))
    (preparedProjections :
      (header.named.inputs.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
        .ok (header.named.inputs.map Prod.snd)) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd) := by
  have binders := header.parameters.symm.trans header.agreement.parameters
  have raw : header.bindings.map (fun binding => binding.1.scheme.body) =
      header.named.inputs.map (fun binding => binding.1.scheme.body) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) binders
  rw [raw, header_native_types header parameterPack]
  exact preparedProjections

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedParameterPackingFacts
