import Solcore.SourceSemantics.CoreLowering.CompatiblePatternValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap

/-! Packed direct inputs are separated by their authentic Source row. An
empty row and a singleton Unit row stay distinct, while a singleton function
or product is retained whole. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursivePublicPackedArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

private theorem unpack_types (types : List TypeSystem.Ty) :
    SourceCoreCompatibleDataMatches.unpackTypes types.length (TypeSystem.Ty.productMany types) = some types := by
  induction types with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => rfl
    | cons next tail =>
      have tailEq : SourceCoreCompatibleDataMatches.unpackTypes (tail.length + 1)
          (TypeSystem.Ty.productMany (next :: tail)) = some (next :: tail) := ih
      simp only [List.length_cons, TypeSystem.Ty.productMany,
        SourceCoreCompatibleDataMatches.unpackTypes, tailEq]
      rfl


variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

/-- The caller supplies the actual parameter row, never a count inferred from
the packed type or native carrier shape. -/
theorem values (types : List TypeSystem.Ty)
    {source : Dynamic.Value} {native : Value} {type : Core.Ty}
    (represented : ValueRep checked registry functions mapping world
      (TypeSystem.Ty.productMany types) source native type) :
    ∃ sources natives nativeTypes,
      ValuesRep checked registry functions mapping world types sources natives nativeTypes ∧
      Dynamic.ValuesPack sources source ∧ native = DataPatternValues.packValues natives ∧
      type = SourceCoreCompatibleCatalog.packTypes nativeTypes :=
  CompatiblePatternValues.unpack (unpack_types types) represented

/-- Both rows already describe the authentic emitted binding list. -/
theorem of_values (bindings : List CallableIndexedParameterCertificates.Binding)
    {sources : List Dynamic.Value} {natives : List Value}
    (represented : ValuesRep checked registry functions mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) sources natives (bindings.map Prod.snd)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world bindings sources natives := by
  induction bindings generalizing sources natives with
  | nil => cases represented; exact .nil
  | cons binding rest ih =>
    cases represented with
    | cons head tail => exact .cons head (ih tail)

private theorem at_bindings (bindings : List CallableIndexedParameterCertificates.Binding)
    (projected : ∀ binding ∈ bindings, checked.catalog.project binding.1.scheme.body = .ok binding.2)
    {sources : List Dynamic.Value} {natives : List Value} {nativeTypes : List Core.Ty}
    (represented : ValuesRep checked registry functions mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) sources natives nativeTypes) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world bindings sources natives := by
  induction bindings generalizing sources natives nativeTypes with
  | nil => cases represented; exact .nil
  | cons binding rest ih =>
    cases represented with
    | cons head tail =>
      have same := Except.ok.inj (head.projection.symm.trans (projected binding (.head _)))
      subst_vars
      exact .cons head (ih (fun item member => projected item (.tail _ member)) tail)

/-- Exact emitted binder projections identify the native row of the same
ordered values without changing their raw Source types. -/
theorem arguments (bindings : List CallableIndexedParameterCertificates.Binding)
    (projected : ∀ binding ∈ bindings, checked.catalog.project binding.1.scheme.body = .ok binding.2)
    {source : Dynamic.Value} {native : Value} {type : Core.Ty}
    (represented : ValueRep checked registry functions mapping world
      (TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body))) source native type) :
    ∃ sources natives,
      Dynamic.ValuesPack sources source ∧ native = DataPatternValues.packValues natives ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world bindings sources natives := by
  obtain ⟨sources, natives, nativeTypes, rows, packing, nativeEq, _type⟩ := values _ represented
  exact ⟨sources, natives, packing, nativeEq, at_bindings bindings projected rows⟩

end Solcore.SourceSemantics.CoreLowering.RecursivePublicPackedArguments
