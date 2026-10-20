import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareParameterTyped
import Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysicalExtension
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameters

/-! Real named parameter allocation initializes the mixed lexical authority.
The named seed is retained explicitly from the compiler hook, and every Source
binder and marked native cell comes from the actual parameter prefix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedParameterEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion CallableIndexedParameterMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedAdmittedBodyEntries

private theorem monomorphic_context {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context parameters types final)
    (initial : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    ∀ id scheme, (id, scheme) ∈ final.locals → scheme.quantified = [] := by
  induction extended with
  | nil => exact initial
  | @cons context binder next rest types final payload mono head tail ih =>
    apply ih
    cases head
    intro id scheme member
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [mono, TypeSystem.Scheme.mono]
    · exact initial id scheme member

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type definitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) definitions := by
  induction related with
  | nil suffixTyped => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed suffixTyped)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions}

/-- This is the actual prefix result, before any body execution or completion. -/
theorem parameters_selected
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (sourceTyping : SelectedCompilationNamedSourceTyping.Certified header)
    (empty : header.function.context.locals = [])
    (ownership : LocalIdentityOwnership header.function.source)
    (native : NativeFrame) (id : Word)
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some id)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named id) (some (CallableIndexedNamedGeneration.state header.named)))
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {administrative actualContext : Core.Context} {canonical actual : Environment} {embedding : Renaming}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative [] [] canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
      mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (agrees : EnvironmentsAgree embedding (DataPatternValues.packValues payloads :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (location : Core.Location)
    (reference : canonical[compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : location ∉ mapping)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      (protocol headers keys) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
    (initial : State headers keys ⟨[], mapping, world, heap, store, canonical⟩)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer location native) :
    ∃ environment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] heap header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (CellAwareParameterTyped.prefixContext header.bindings actualContext)
        compiled.indexed.layouts.definitions ∧
      ContinuationAgreement actual store (header.parameterCode.rename embedding)
        finalActual finalStore (header.body.rename finalEmbedding) ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world heap store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates initial reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = location ∧ physical.native = native := by
  have accepted := header.acceptedPrefix
  rw [sameLayouts, sameGlobals] at accepted
  have tree := CallableIndexedParameterCertificates.of_accepted header.onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues payloads :: canonical) := by intro index value found; exact found
  have length : (header.bindings.map Prod.snd).length = payloads.length := by simpa using represented.length.2
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, storeExtension,
      _lookups, actualLayout, spine, finalTyped, agreement, reached, related⟩ :=
    CellAwareParameterTyped.Stateful.prefix_typed tree GeneralizedLocalDescriptorHeap.ordinary_cells
      (protocol headers keys) producer rfl header.registered represented environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using reference) read unmapped initial ready
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (header.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = header.bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical header.bindings.length
      (DataPatternValues.packValues payloads) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  rw [← header.parameters] at allocated
  have sourceReceipt := SelectedCompilationNamedAdmission.parameter_source sourceTyping allocated heapTyped argumentsTyped
  have metadata := GenericLexicalContext.binders_metadata allocated
  have monomorphic := monomorphic_context header.extended (by intro id scheme member; rw [empty] at member; cases member)
  have authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      header.named.signature.key [] finalMap finalWorld finalHeap finalStore environment :=
    CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  have finalReference : finalLogical[header.bindings.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location) := by
    rw [logicalEq]
    have index : header.bindings.length + 1 + compiled.indexed.base.globals.length =
        added.length + (compiled.indexed.base.globals.length + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨stillUnmapped, stillRead⟩ := preservation location unmapped (List.getElem?_eq_some_iff.mp read).1
  have sourceEq : header.function.source = CallableIndexedNamedGeneration.source header.named := header.agreement.source
  let physical : CellAwareScopePhysical.Physical compiled header.named header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      finalLogical finalMap finalWorld finalHeap finalStore environment := CellAwareScopePhysical.Physical.of_monomorphic native id selected carried
    (by simpa only [← sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using (RecursiveNamedHeaderScopeDeclarations.header_scope (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header))
    (sourceEq ▸ ownership)
    (by simpa only [← sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using (CellAwareScopeDeclarations.header_scope (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header))
    location (by simpa using finalReference) (stillRead.trans read) stillUnmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  obtain ⟨suffix, storeEq⟩ := storeExtension
  have effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store finalMap finalWorld finalHeap finalStore := by
    rw [storeEq]
    exact .append store suffix metadata maps worlds
  refine ⟨environment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
    allocated, (by simpa only [List.append_nil] using finalWithBundle), finalHeaps, sourceReceipt, actualLayout, finalTyped, agreement, preservation,
    effect, authority, reached, related, physical, rfl, rfl⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
theorem parameters
    (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (wellFormed : ProgramWellFormed program)
    (empty : header.function.context.locals = [])
    (ownership : LocalIdentityOwnership header.function.source)
    (native : NativeFrame) (id : Word)
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some id)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named id) (some (CallableIndexedNamedGeneration.state header.named)))
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {administrative actualContext : Core.Context} {canonical actual : Environment} {embedding : Renaming}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative [] [] canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
      mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (agrees : EnvironmentsAgree embedding (DataPatternValues.packValues payloads :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (location : Core.Location)
    (reference : canonical[compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : location ∉ mapping)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      (protocol headers keys) compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
    (initial : State headers keys ⟨[], mapping, world, heap, store, canonical⟩)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer location native) :
    ∃ environment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] heap header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (CellAwareParameterTyped.prefixContext header.bindings actualContext)
        compiled.indexed.layouts.definitions ∧
      ContinuationAgreement actual store (header.parameterCode.rename embedding)
        finalActual finalStore (header.body.rename finalEmbedding) ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world heap store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates initial reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = location ∧ physical.native = native := by
  apply parameters_selected (sourceTyping := RecursiveNamedHeaderSourceTyping.certificate header wellFormed)  <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedParameterEntry
