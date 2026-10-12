import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncoding
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedLeafMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedRawInputs

/-! One actual startup input may contain issued functions at arbitrary finite
depth. The original codec and genuine leaf issuance construct its complete
receiving representation and independent Source typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionState (State)
open CallableIndexedOwnedFunctionValues (Header)

theorem StartAt.nested_argument_represents
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : Inventory inputs)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : State (headers rows) (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (callerHeader : Header compiled (Program.ofChecked compiled.sourceProgram))
    {artifact : Artifact} {session : Session artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root recipe.compiled}
    {native : Environment} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key publicArguments fuel checkpoint recipe root
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) native encodedValues)
    {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value} {source : Dynamic.Value} {index : Nat}
    (rawType : root.inputs[index]? = some sourceType)
    (found : publicArguments[index]? = some publicValue)
    (receipt : RecursiveNamedPublicNestedInputs.Input rows session callerHeader.function.context
      sourceType publicValue source)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ value type, native[index]? = some value ∧ compiled.compatible.checked.catalog.project sourceType = .ok type ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
          bodyRegistry faults profile)
        [] ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
        sourceType source value type ∧
      Dynamic.ValueHasType callerHeader.function.context ⟨[]⟩ source sourceType := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨before, encoded, type, valueAt, typeAt, projected, owner, accepted, extended⟩ :=
    RecursiveNamedPublicNestedRawInputs.StartAt.raw_input started rawType found
  obtain ⟨actual, actualAt, typed⟩ := started.typed.lookup typeAt
  have sameValue : actual = encoded.value := Option.some.inj (actualAt.symm.trans valueAt)
  subst actual
  have leaves := fun {type value source}
      (leaf : RecursiveNamedPublicMixedArgumentReceipts.Input rows session callerHeader.function.context type value source) =>
    RecursiveNamedPublicNestedLeafMeaning.leaf_meaning prepared inputs rows bodyRegistry registry faults profile
      caller callerHeader started.recipe_eq leaf wellFormed
  have represented := RecursiveNamedPublicNestedEncoding.Input.represents receipt started.recipe_eq
    (fun leaf => (leaves leaf).1) owner rfl accepted projected typed (extended.trans metadata)
  exact ⟨encoded.value, type, valueAt, projected, represented,
    RecursiveNamedPublicNestedInputs.Input.source_hasType receipt (fun leaf => (leaves leaf).2)⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentReceipts
