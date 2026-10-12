import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContext

/-! Function leaves obtain their meaning from actual issued factories and the
initialized owned caller. Nested encoding selects the same authenticated
callable independently of its validation fuel or intermediate metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedLeafMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicNestedEncodingContext
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionState (State)
open CallableIndexedOwnedFunctionValues (Header)

theorem leaf_meaning {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    {artifact : Artifact} {session : Session artifact}
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
    (atRecipe : ArtifactRecipe artifact recipe)
    {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (receipt : RecursiveNamedPublicMixedArgumentReceipts.Input rows session callerHeader.function.context
      sourceType publicValue source)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    RawMeaning session
      (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
        bodyRegistry faults profile) registry []
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      sourceType publicValue source ∧
    Dynamic.ValueHasType callerHeader.function.context ⟨[]⟩ source sourceType := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  cases receipt with
  | data inputTyped meaning =>
      refine ⟨?_, RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped.source_hasType inputTyped meaning⟩
      intro fuel before expected encoded type owner compatible accepted projected typed metadata
      obtain ⟨carrier, image, _typed⟩ := inputTyped
      have encodedAt := accepted.data owner ⟨carrier, image⟩
      obtain ⟨interpreted, interpretedAt, represented⟩ :=
        RecursiveNamedPublicDataInputs.EncodedDataInput.represents
          (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
            bodyRegistry faults profile) []
          ((RecursiveNamedCatalogPreparedInitialization.store recipe.compiled).map Core.Value.type)
          encodedAt projected (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).basePrefix typed
      have same := RecursiveNamedPublicRuntimeMeaning.means_functional interpretedAt meaning
      subst interpreted
      exact .compatible compatible.symm (represented.extend metadata (.refl _) (.refl _))
  | named packet member issuance continued handleValue =>
      obtain ⟨callable, imported, represented, sourceTyped⟩ :=
        RecursiveNamedPublicNamedArgumentReceipts.Session.named_value_represents_after
          prepared inputs rows packet member bodyRegistry registry faults profile caller callerHeader
          issuance continued rfl handleValue wellFormed
      refine ⟨?_, sourceTyped⟩
      intro fuel before expected encoded type owner compatible accepted projected typed metadata
      rw [handleValue] at accepted
      have sameValue := accepted.function_eq imported
      have actualProjection := (CompatibleEncoding.project_compatible compatible).symm.trans projected
      have sameType := Except.ok.inj (represented.projection.symm.trans actualProjection)
      rw [sameValue]
      exact sameType ▸ represented
  | builtin issuance continued handleValue =>
      obtain ⟨callable, _same, _sourceType, imported, represented, sourceTyped⟩ :=
        RecursiveNamedPublicBuiltinArgumentReceipts.Session.builtin_value_represents_after
          prepared (headers rows) (keys recipe.compiled) bodyRegistry registry faults profile
          [] callerHeader.function.context ⟨[]⟩ issuance continued rfl handleValue
          (world := (RecursiveNamedCatalogPreparedInitialization.store recipe.compiled).map Core.Value.type)
      refine ⟨?_, sourceTyped⟩
      intro fuel before expected encoded type owner compatible accepted projected typed metadata
      rw [handleValue] at accepted
      have sameValue := accepted.function_eq imported
      have actualProjection := (CompatibleEncoding.project_compatible compatible).symm.trans projected
      have sameType := Except.ok.inj (represented.projection.symm.trans actualProjection)
      rw [sameValue]
      exact sameType ▸ represented

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedLeafMeaning
