import Solcore.SourceSemantics.CoreLowering.CellAwareNamedEntry

/-! The named entry of an accepted call, over any generalized instance model of
the caller's cells. It is `CellAwareNamedEntry.prepare_selected` with two more
receipts: the parameter spine of the canonical environment, which places the
callee capture's global slots after the parameters, and a sized inversion of
native completion into a strictly smaller body completion. The parameter
prefix agreement is sized for that purpose (`SizedAgreement`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataEquality
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedAllocationCompletion
open CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedAdmittedBodyEntries
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

/-- A finite prefix around a continuation: wrapping is exact, and a sized
completion of the whole unwraps to a continuation completion no larger. -/
structure SizedAgreement (environment : Environment) (store : Store) (whole : Expr)
    (nextEnvironment : Environment) (nextStore : Store) (next : Expr) : Prop where
  wrap : ∀ {result finalStore}, Evaluates nextEnvironment nextStore next result finalStore →
    Evaluates environment store whole result finalStore
  unwrap : ∀ {size result finalStore}, EvaluationSize size environment store whole result finalStore →
    ∃ smaller, smaller ≤ size ∧ EvaluationSize smaller nextEnvironment nextStore next result finalStore

namespace SizedAgreement

theorem refl (environment : Environment) (store : Store) (code : Expr) :
    SizedAgreement environment store code environment store code :=
  ⟨id, fun evaluation => ⟨_, Nat.le_refl _, evaluation⟩⟩

theorem trans {environment middleEnvironment nextEnvironment : Environment}
    {store middleStore nextStore : Store} {whole middle next : Expr}
    (first : SizedAgreement environment store whole middleEnvironment middleStore middle)
    (second : SizedAgreement middleEnvironment middleStore middle nextEnvironment nextStore next) :
    SizedAgreement environment store whole nextEnvironment nextStore next := by
  refine ⟨fun evaluation => first.wrap (second.wrap evaluation), ?_⟩
  intro size result finalStore evaluation
  obtain ⟨middleSize, middleLe, middleEvaluation⟩ := first.unwrap evaluation
  obtain ⟨nextSize, nextLe, nextEvaluation⟩ := second.unwrap middleEvaluation
  exact ⟨nextSize, Nat.le_trans nextLe middleLe, nextEvaluation⟩

theorem letE {environment : Environment} {before middle : Store} {initializer body : Expr} {value : Value}
    (evaluated : Evaluates environment before initializer value middle) :
    SizedAgreement environment before (.letE initializer body) (value :: environment) middle body := by
  refine ⟨fun body => .letE evaluated body, ?_⟩
  intro size result finalStore evaluation
  obtain ⟨smaller, less, body⟩ := evaluation.let_body evaluated
  exact ⟨smaller, Nat.le_of_lt less, body⟩

theorem bind {environment : Environment} {before middle : Store} {computation body : Expr} {type : Ty}
    {value : Value} (evaluated : Evaluates environment before computation (.inRight .word value) middle) :
    SizedAgreement environment before (LanguageResult.bind type computation body) (value :: environment) middle body := by
  refine ⟨fun body => LanguageResult.bind_success type evaluated body, ?_⟩
  intro size result finalStore evaluation
  obtain ⟨smaller, less, body⟩ := evaluation.bind_success evaluated
  exact ⟨smaller, Nat.le_of_lt less, body⟩

end SizedAgreement

private theorem selects_rename {environment target : Environment} {expression : Expr} {value : Value} {ξ : Renaming}
    (selected : Selects environment expression value) (agrees : EnvironmentsAgree ξ environment target) :
    Selects target (expression.rename ξ) value := by
  induction selected with
  | var found => exact .var (agrees found)
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

private theorem agree_insert {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (value : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical (value :: actual) := by
  intro index selected found
  exact agrees found

/-- `CellAwareParameterTyped.Stateful.prefix_typed` with a sized agreement. -/
theorem prefix_sized {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {total : Nat} {output : Ty} {body : Expr}
    {scope : Scope} {start : Nat} {bindings : List Binding} {code : Expr}
    (tree : Tree layouts owner active layout globals onError source total output body scope start bindings code)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {nativeDefinitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects nativeDefinitions}
    {cells : GenericHeap.CellModel nativeDefinitions}
    (ordinaryCells : GenericHeap.OrdinaryCells model cells)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol layouts layout cells)
    (definitions : layouts.definitions = nativeDefinitions)
    (registered : layout.Registered nativeDefinitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical logical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming}
    {allTypes : List Ty} {allValues : List Value} {named : Bool} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical nativeDefinitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (sourceLayout : EnvironmentsAgree (Renaming.insertion start) canonical logical)
    (actualLayout : EnvironmentsAgree ξ logical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext nativeDefinitions)
    (bundleSlot : logical[start]? = some (DataPatternValues.packValues allValues))
    (total_eq : total = allTypes.length)
    (bundleLength : allTypes.length = allValues.length)
    (valuesSelected : ∀ {index value}, values[index]? = some value → allValues[start + index]? = some value)
    (kinds : ∀ binding ∈ bindings, source.inputs.any (fun input => decide (input.id = binding.1.id)) = named)
    (reference : canonical[scope.length + (if named then 0 else 1) + globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt (catalog := catalog) producer contextLocation native) :
    ∃ finalEnvironment finalHeap finalCanonical finalLogical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate environment heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrative
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical nativeDefinitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      (∃ suffix, finalStore = store ++ suffix) ∧
      EnvironmentsAgree (DataMatchCoreAllocation.liftMany bindings.length (Renaming.insertion start))
        finalCanonical finalLogical ∧
      EnvironmentsAgree finalEmbedding finalLogical finalActual ∧
      (∃ added : Environment, added.length = bindings.length ∧
        finalCanonical = added ++ canonical ∧ finalLogical = added ++ logical) ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (CellAwareParameterTyped.prefixContext bindings actualContext)
        nativeDefinitions ∧
      SizedAgreement actual store (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
          finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩ := by
  induction tree generalizing mapping world environment canonical logical actual heap store ξ sources values actualContext with
  | nil =>
    cases represented
    exact ⟨environment, heap, canonical, logical, actual, store, mapping, world, ξ,
      .nil _ _, environments, heaps, .refl _, .refl _, .refl _ _, ⟨[], by simp⟩, sourceLayout, actualLayout,
      ⟨[], rfl, rfl, rfl⟩, actualTyped, SizedAgreement.refl _ _ _, ⟨initial, protocol.refl initial⟩⟩
  | @cons scope start binder payload bindings next allocation annotation same tail ih =>
    cases represented with
    | @cons _ _ sourceValue value _ sourceValues nativeValues head rest =>
      have selected : allValues[start]? = some value := by simpa using valuesSelected (index := 0) rfl
      have projection := DataPatternValues.projectPacked_selects (Selects.var bundleSlot) bundleLength start selected
      rw [← FunctionArguments.argumentProjection_eq, ← total_eq] at projection
      have initializer : Evaluates actual store
          ((LanguageResult.success (SourceCoreFunctions.argumentProjection start total (.var start))).rename ξ)
          (.inRight .word value) store := .inRight ((selects_rename projection actualLayout).evaluates store)
      have canonicalLayout : EnvironmentsAgree (request source scope start (binder, payload)).references
          canonical (value :: logical) := agree_insert sourceLayout value
      have referenceAt : (value :: logical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals
          (request source scope start (binder, payload))]? = some (.cellRef layout.type contextLocation) := by
        have found := canonicalLayout reference
        have kind := kinds (binder, payload) (by simp)
        change source.inputs.any (fun input => decide (input.id = binder.id)) = named at kind
        have isNamed : SourceCoreCallableIndexedAllocationFrames.isNamedInput
            (request source scope start (binder, payload)) = named := kind
        simp only [SourceCoreCallableIndexedAllocationFrames.referenceIndex, isNamed]
        exact found
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextHeaps, nextReference, frame,
        nextState, nextRelated⟩ :=
        producer.complete allocation annotation same definitions registered environments
          canonicalLayout heaps referenceAt read (.initialized rfl rfl)
          (ordinaryCells.inject (.initialized head)) (.ordinary Dynamic.Heap.Allocates.append)
          initial (readyAt initial read)
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      have nextEnvironments := CallableIndexedOrdinaryAllocation.bind_environment (id := binder.id) environments
        nextReference
      have nextSourceLayout : EnvironmentsAgree (Renaming.insertion (start + 1))
          (nextRef :: canonical) (nextRef :: logical) := by
        intro index selectedValue found
        have selected := sourceLayout.lift nextRef found
        simpa only [Renaming.lift_insertion] using selected
      have nextActualLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ).lift
          (nextRef :: logical) (nextRef :: value :: actual) := by
        have inserted : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) logical (value :: actual) :=
          agree_insert actualLayout value
        intro index selectedValue found
        exact inserted.lift nextRef found
      have renamedAllocation := CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl)
        allocationEval (actualLayout.lift value)
      have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
      obtain ⟨stillUnmapped, stillRead⟩ := frame contextLocation unmapped bound
      have nextRead := stillRead.trans read
      have nextSelected : ∀ {index selectedValue}, nativeValues[index]? = some selectedValue →
          allValues[(start + 1) + index]? = some selectedValue := by
        intro index selectedValue found
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valuesSelected (index := index + 1) found
      obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds,
        finalFrame, storeExtension, finalSourceLayout, finalActualLayout, spine, finalTyped, agreement, finalState,
        finalRelated⟩ :=
        ih (rest.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
          (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
            from ⟨_, rfl⟩))
          nextEnvironments nextHeaps nextSourceLayout nextActualLayout
          (show RuntimeEnvironmentHasTypes
              (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
              (nextRef :: value :: actual) (OptionalCell.referenceType payload :: payload :: actualContext)
              nativeDefinitions from
            .cons (.cellRef nextReference.typed)
              (.cons ((model.runtime_hasType head).weaken ⟨_, rfl⟩) (actualTyped.weaken ⟨_, rfl⟩)))
          (show (nextRef :: logical)[start + 1]? = some (DataPatternValues.packValues allValues) from bundleSlot)
          nextSelected (fun binding member => kinds binding (List.mem_cons_of_mem _ member))
          (show (nextRef :: canonical)[(((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals)]? =
            some (.cellRef layout.type contextLocation) from by
              have nextIndex : (((binder.id, payload) :: scope).length + (if named then 0 else 1) + globals) =
                  (scope.length + (if named then 0 else 1) + globals) + 1 := by simp only [List.length_cons]; omega
              rw [nextIndex]
              exact reference)
          nextRead stillUnmapped nextState
      refine ⟨finalEnvironment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore,
        finalMap, finalWorld, finalEmbedding, .cons .append allocated, finalEnvironments, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [layout.type, allocation.entry.layout.type, OptionalCell.cellType payload])
          from ⟨_, rfl⟩).trans worlds,
        frame.trans finalFrame, ?_, ?_, finalActualLayout, ?_, finalTyped, ?_,
        ⟨finalState, protocol.trans nextRelated finalRelated⟩⟩
      · obtain ⟨suffix, storeEq⟩ := storeExtension
        exact ⟨_, storeEq.trans (List.append_assoc _ _ _)⟩
      · intro index selectedValue found
        simpa only [List.length_cons, DataMatchCoreAllocation.liftMany, Renaming.lift_insertion] using
          finalSourceLayout found
      · obtain ⟨added, length, canonicalEq, logicalEq⟩ := spine
        exact ⟨added ++ [nextRef], by simp [length], by simpa [List.append_assoc, nextRef, request] using canonicalEq,
          by simpa [List.append_assoc, nextRef, request] using logicalEq⟩
      · simp only [LoopStatements.rename_insert_lift] at agreement
        apply SizedAgreement.trans ?_ agreement
        simpa only [LanguageResult.bind, Expr.rename, Renaming.lift, LoopRenaming.weakenOne, nextRef, request] using
          (SizedAgreement.bind initializer).trans (SizedAgreement.letE renamedAllocation)

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

section Entry
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel compiled.indexed.layouts.definitions}

/-- `CellAwareNamedParameterEntry.parameters_selected` over any instance model,
with the parameter spine and a sized agreement. -/
theorem parameters
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
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances)
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
      (GeneralizedLocalDescriptorHeap.cellModel model instances))
    (initial : State headers keys ⟨[], mapping, world, heap, store, canonical⟩)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer location native) :
    ∃ environment finalHeap finalCanonical finalActual finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] heap header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances)
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual (CellAwareParameterTyped.prefixContext header.bindings actualContext)
        compiled.indexed.layouts.definitions ∧
      SizedAgreement actual store (header.parameterCode.rename embedding)
        finalActual finalStore (header.body.rename finalEmbedding) ∧
      (∃ added : Environment, added.length = header.bindings.length ∧
        finalCanonical = added ++ DataPatternValues.packValues payloads :: canonical) ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At instances header.named.signature.key []
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
  obtain ⟨environment, finalHeap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld,
      finalEmbedding, allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, storeExtension,
      _lookups, actualLayout, spine, finalTyped, agreement, reached, related⟩ :=
    prefix_sized tree GeneralizedLocalDescriptorHeap.ordinary_cells
      (protocol headers keys) producer rfl header.registered represented environments heaps
      sourceLayout agrees actualTyped (allTypes := header.bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds header.inputs)
      (by simpa using reference) read unmapped initial ready
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (header.bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length =
      header.bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical header.bindings.length
      (DataPatternValues.packValues payloads) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  rw [← header.parameters] at allocated
  have sourceReceipt := SelectedCompilationNamedAdmission.parameter_source sourceTyping allocated heapTyped argumentsTyped
  have metadata := GenericLexicalContext.binders_metadata allocated
  have monomorphic := monomorphic_context header.extended (by intro id scheme member; rw [empty] at member; cases member)
  have authority : CellAwareScopeAuthority.At instances
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
      finalLogical finalMap finalWorld finalHeap finalStore environment :=
    CellAwareScopePhysical.Physical.of_monomorphic native id selected carried
    (by simpa only [← sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using
      (RecursiveNamedHeaderScopeDeclarations.header_scope (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        header))
    (sourceEq ▸ ownership)
    (by simpa only [← sourceEq, RecursiveNamedCatalogNativeContexts.bodyScope] using
      (CellAwareScopeDeclarations.header_scope (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        header))
    location (by simpa using finalReference) (stillRead.trans read) stillUnmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  obtain ⟨suffix, storeEq⟩ := storeExtension
  have effect : CellAwareScopeAuthority.Effect instances
      mapping world heap store finalMap finalWorld finalHeap finalStore := by
    rw [storeEq]
    exact .append store suffix metadata maps worlds
  refine ⟨environment, finalHeap, finalLogical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
    allocated, (by simpa only [List.append_nil] using finalWithBundle), finalHeaps, sourceReceipt, actualLayout,
    finalTyped, agreement, ⟨added, prefixLength, logicalEq⟩, preservation, effect, authority, reached, related,
    physical, rfl, rfl⟩

variable {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : CallableIndexedOwnedFunctionValues.Header compiled program)
  (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}

/-- `CellAwareNamedEntry.prepare_selected` over any instance model of the
caller's cells, with the parameter spine and a sized inversion of native
completion. -/
theorem prepare
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (sameGlobals : header.globals = compiled.indexed.base.globals.length)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      header.named.signature.key = .ok header.named.specialized)
    (sourceTyping : SelectedCompilationNamedSourceTyping.Certified header)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances)
      mapping world before store)
    (stable : StableRows caller) :
    ∃ environment finalHeap finalCanonical finalActual finalContext finalStore finalMap finalWorld finalEmbedding,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment finalHeap ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
        finalMap finalWorld (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        environment finalCanonical compiled.indexed.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances)
        finalMap finalWorld finalHeap finalStore ∧
      SourceReceipt program header.function header.context environment finalHeap ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext compiled.indexed.layouts.definitions ∧
      (∃ added : Environment, added.length = header.bindings.length ∧
        finalCanonical = added ++ DataPatternValues.packValues payloads :: capture.canonical) ∧
      AdministrativePreserved mapping
        (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame compiled.indexed.ancestry.graph.table
            ((compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key)).getD
              Word.zero))))
        finalMap finalStore ∧
      CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld finalHeap finalStore ∧
      CellAwareScopeAuthority.At instances header.named.signature.key []
        finalMap finalWorld finalHeap finalStore environment ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        Relates caller reached ∧ StableRows reached ∧
      ∃ physical : CellAwareScopePhysical.Physical compiled header.named header.context
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          finalCanonical finalMap finalWorld finalHeap finalStore environment,
        physical.location = owner.key.frameLocation ∧
      (∀ {value bodyStore}, Evaluates finalActual finalStore (header.body.rename finalEmbedding) value bodyStore →
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value
          (bodyStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current))) ∧
      (∀ {size value bodyStore}, EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value bodyStore →
        ∃ smaller reachedStore, smaller < size ∧
          EvaluationSize smaller finalActual finalStore (header.body.rename finalEmbedding) value reachedStore ∧
          bodyStore = reachedStore.set owner.key.frameLocation
            (encode compiled.indexed.ancestry.layout.frame (caller.rows owner.position).authority.current)) := by
  have originalTyping := sourceTyping
  obtain ⟨_facts, certified⟩ := originalTyping
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certified.locals_empty
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certified.local_identity_ownership
  let row := caller.rows owner.position
  have rowLocation : row.authority.frameLocation = owner.key.frameLocation := row.frame_eq
  have unmapped : owner.key.frameLocation ∉ mapping := by simpa only [rowLocation] using row.authority.unmapped
  have current : store.read? owner.key.frameLocation =
      some (encode compiled.indexed.ancestry.layout.frame row.authority.current) := by
    simpa only [rowLocation] using row.authority.frame.read
  obtain ⟨origin, index, selected, frame, emitted⟩ :=
    CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry header.hook
  have history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (.state index) (.named origin) (some (CallableIndexedNamedGeneration.state header.named)) := by
    rw [← frame]
    exact named_complete compiled.indexed.ancestry.graph
      (CallableIndexedNamedGeneration.seed compiled.indexed selected record)
  let installed := install caller owner.position (.stable history)
  have written : store.write? owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)) =
      some (store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp current).1, rfl⟩
  have referenceTyped : world[owner.key.frameLocation]? = some compiled.indexed.ancestry.layout.frame.type := by
    simpa only [rowLocation] using row.authority.typed
  have installedHeaps := heaps.write_administrative
    (fun found => unmapped (List.mem_of_getElem? found)) referenceTyped
    (encode_runtime_typed world header.registered (.state index)) written
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) headers keys
    (GeneralizedLocalDescriptorHeap.cellModel model instances)
  let initial : State headers keys ⟨[], mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)),
      capture.canonical⟩ := installed
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer owner.key.frameLocation (.state index) := by
    intro index reached read
    exact CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position read history
  let actual := .unit :: encode compiled.indexed.ancestry.layout.frame row.authority.current ::
    DataPatternValues.packValues payloads :: capture.captured
  let embedding := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift)
  have layout : EnvironmentsAgree embedding (DataPatternValues.packValues payloads :: capture.canonical) actual :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix
        (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame row.authority.current)) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := compiled.indexed.layouts.definitions))
    (.cons (encode_runtime_typed world header.registered row.authority.current)
      (.cons (CallableIndexedParameters.Arguments.pack_typed represented) capture.typed))
  obtain ⟨environment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld, finalEmbedding,
      allocated, environments, finalHeaps, sourceReceipt, agrees, finalTyped, agreement, spine, preserved,
      effect, lexical, reached, related, physical, locationEq, _nativeEq⟩ :=
    parameters header sameLayouts sameGlobals sourceTyping empty ownership (.state index) origin selected history
      represented capture.environments installedHeaps heapTyped argumentsTyped layout actualTyped
      owner.key.frameLocation (by simpa only [sameGlobals] using capture.reference)
      (Store.write?_reads_written written) unmapped producer initial ready
  have finalStable := GeneralizedLocalParameterAdmission.after_parameters caller reached owner.position
    (fun i _ => stable i) history preserved
  have fullEffect := (CellAwareScopeAuthority.Effect.set_unmapped store
    (encode compiled.indexed.ancestry.layout.frame (.state index)) unmapped).trans effect
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have next : Evaluates (encode compiled.indexed.ancestry.layout.frame row.authority.current ::
      DataPatternValues.packValues payloads :: capture.captured) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates _ _ _ _
  refine ⟨environment, finalHeap, finalCanonical, finalActual, _, finalStore, finalMap, finalWorld, finalEmbedding,
    allocated, environments, finalHeaps, sourceReceipt, agrees, finalTyped, spine, ?_, fullEffect, lexical,
    reached, (install_related caller owner.position (.stable history)).trans related, finalStable,
    physical, locationEq, ?_, ?_⟩
  · simpa only [selected, Option.getD_some, frame] using preserved
  · intro value bodyStore evaluated
    have parameterRun := agreement.wrap evaluated
    simp only [embedding, GenericExpressionMeaning.rename_prefix] at parameterRun
    rw [renamed]
    exact CallableContextFrames.withFrame_evaluates (.var reference) current next parameterRun
  · intro size value bodyStore evaluated
    rw [renamed] at evaluated
    obtain ⟨_nextSize, child, installedValue, nextStore, reachedStore, actualNext, parameterRun, _nextLess,
        childLess, restored⟩ :=
      RecursiveNamedCallBounds.with_frame (.var reference) current evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic actualNext.sound next
    have parameterSized : EvaluationSize child actual
        (nextStore.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)))
        (header.parameterCode.rename embedding) value reachedStore := by
      simpa only [embedding, GenericExpressionMeaning.rename_prefix] using parameterRun
    obtain ⟨smaller, smallerLe, bodyRun⟩ := agreement.unwrap parameterSized
    exact ⟨smaller, reachedStore, Nat.lt_of_le_of_lt smallerLe childLess, bodyRun, restored⟩

end Entry

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedEntry
