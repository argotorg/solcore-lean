import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.GenericCellHeap
import Solcore.SourceSemantics.CoreLowering.RecursivePublicApplicationResult
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputCollection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicOutputSelections
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedHistoryEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap

/-!
# Cell-aware public histories

The function history of a public session and its physical form, with the scope authority, declarations and physical scope that a public result retains.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority
/-! Lexical authority retains each actual generalized declaration's complete
compiler binding and native row. Transport requires a concrete effect on that
row; administrative preservation alone does not preserve mapped payloads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts

variable {definitions : DataEnvironment} {instances : InstanceModel definitions}

private theorem located_same {function binding lexical location mapping world heap store nextMap nextWorld after finalStore}
    (located : Located instances function binding lexical location mapping world heap store)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (read : finalStore.read? located.target = some (.inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value located.values))) :
    ∃ next : Located instances function binding lexical location nextMap nextWorld after finalStore,
      next.values = located.values := by
  obtain ⟨cell, sourceRead, _, descriptor⟩ := metadata location located.cell located.sourceRead
  have extendRows : ∀ {candidates values},
      SourceCoreLocalPolymorphism.ProductBundle.Pointwise
        (instances.Represents mapping world function binding lexical) candidates values →
      SourceCoreLocalPolymorphism.ProductBundle.Pointwise
        (instances.Represents nextMap nextWorld function binding lexical) candidates values := by
    intro candidates values rows
    induction rows with
    | nil => exact .nil
    | cons head _ ih => exact .cons (instances.extend head maps worlds) ih
  have rows := extendRows located.rows
  exact ⟨⟨located.attachment, cell, sourceRead, descriptor.trans located.descriptor,
    located.target, ⟨maps.lookup located.reference.mapped, worlds.lookup located.reference.typed⟩,
    located.values, rows, read⟩, rfl⟩

structure Effect (instances : InstanceModel definitions)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (nextMap : LocationMap) (nextWorld : StoreTyping) (after : Dynamic.Heap) (finalStore : Store) : Prop where
  metadata : Dynamic.HeapMetadataExtend heap after
  maps : LocationMap.Extends mapping nextMap
  worlds : WorldExtends world nextWorld
  retains_values : ∀ {function binding lexical location}
    (located : Located instances function binding lexical location mapping world heap store),
    ∃ next : Located instances function binding lexical location nextMap nextWorld after finalStore,
      next.values = located.values

theorem Effect.retains {mapping world heap store nextMap nextWorld after finalStore}
    (effect : Effect instances mapping world heap store nextMap nextWorld after finalStore)
    {function binding lexical location}
    (located : Located instances function binding lexical location mapping world heap store) :
    Nonempty (Located instances function binding lexical location nextMap nextWorld after finalStore) := by
  obtain ⟨next, _⟩ := effect.retains_values located
  exact ⟨next⟩

theorem Effect.refl (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :
    Effect instances mapping world heap store mapping world heap store :=
  ⟨.refl _, .refl _, .refl _, fun located => ⟨located, rfl⟩⟩

theorem Effect.trans {mapping middleMap finalMap : LocationMap} {world middleWorld finalWorld : StoreTyping}
    {heap middleHeap finalHeap : Dynamic.Heap} {store middleStore finalStore : Store}
    (first : Effect instances mapping world heap store middleMap middleWorld middleHeap middleStore)
    (second : Effect instances middleMap middleWorld middleHeap middleStore finalMap finalWorld finalHeap finalStore) :
    Effect instances mapping world heap store finalMap finalWorld finalHeap finalStore := by
  refine ⟨first.metadata.trans second.metadata, first.maps.trans second.maps,
    first.worlds.trans second.worlds, ?_⟩
  intro function binding lexical location located
  obtain ⟨middle, sameMiddle⟩ := first.retains_values located
  obtain ⟨last, sameLast⟩ := second.retains_values middle
  exact ⟨last, sameLast.trans sameMiddle⟩

theorem Effect.append {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
    {heap after : Dynamic.Heap} (store suffix : Store)
    (metadata : Dynamic.HeapMetadataExtend heap after)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    Effect instances mapping world heap store nextMap nextWorld after (store ++ suffix) := by
  refine ⟨metadata, maps, worlds, ?_⟩
  intro function binding lexical location located
  apply located_same located metadata maps worlds
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp located.nativeRead).1).trans located.nativeRead

theorem Effect.set_unmapped {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} (store : Store) {target : Core.Location}
    (value : Core.Value) (unmapped : target ∉ mapping) :
    Effect instances mapping world heap store mapping world heap (store.set target value) := by
  refine ⟨.refl _, .refl _, .refl _, ?_⟩
  intro function binding lexical location located
  have different : target ≠ located.target := by
    intro same
    exact unmapped (same.symm ▸ List.mem_of_getElem? located.reference.mapped)
  apply located_same located (.refl _) (.refl _) (.refl _)
  simpa [Store.read?, different] using located.nativeRead

theorem Effect.write_ordinary {mapping : LocationMap} {world : StoreTyping}
    {heap after : Dynamic.Heap} {store finalStore : Store}
    (injective : LocationMap.Injective mapping)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {target : Core.Location} {payload : Core.Ty}
    (read : Dynamic.Heap.Reads heap location cell) (ordinary : cell.generalized = none)
    (reference : ReferenceRepresents mapping world location target payload)
    {sourceValue : Option Dynamic.Value} {nativeValue : Core.Value}
    (written : Dynamic.Heap.Writes heap location sourceValue after)
    (nativeWritten : store.write? target nativeValue = some finalStore) :
    Effect instances mapping world heap store mapping world after finalStore := by
  refine ⟨.of_write written, .refl _, .refl _, ?_⟩
  intro function binding lexical descriptorLocation located
  have different : descriptorLocation ≠ location := by
    intro same
    subst location
    have cells := located.sourceRead.functional read
    have descriptors := congrArg Dynamic.Cell.generalized cells
    rw [located.descriptor, ordinary] at descriptors
    cases descriptors
  have nativeDifferent : located.target ≠ target := by
    intro same
    have indices := injective (same ▸ located.reference.mapped) reference.mapped
    apply different
    cases descriptorLocation
    cases location
    exact congrArg Dynamic.Location.mk indices
  apply located_same located (.of_write written) (.refl _) (.refl _)
  exact (Store.write?_preserves_other nativeWritten nativeDifferent).trans located.nativeRead

inductive Entry (instances : InstanceModel definitions) (caller : SourceCoreLocalPolymorphism.Key)
    (active : Substitution) (id : Resolved.LocalId) (location : Dynamic.Location)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop where
  | ordinary {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell)
      (descriptor : cell.generalized = none) :
      Entry instances caller active id location mapping world heap store
  | generalized {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
      {lexical : Substitution} (owner : binding.caller = caller) (binder : binding.binder.id = id)
      (context : ContextExtension lexical active)
      (located : Nonempty (Located instances function binding lexical location mapping world heap store)) :
      Entry instances caller active id location mapping world heap store

inductive At (instances : InstanceModel definitions) (caller : SourceCoreLocalPolymorphism.Key)
    (active : Substitution) (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :
    Dynamic.Environment → Prop where
  | nil : At instances caller active mapping world heap store []
  | cons {id : Resolved.LocalId} {location : Dynamic.Location} {rest : Dynamic.Environment}
      (head : Entry instances caller active id location mapping world heap store)
      (tail : At instances caller active mapping world heap store rest) :
      At instances caller active mapping world heap store ((id, location) :: rest)

theorem Entry.transport {caller active id location mapping world heap store nextMap nextWorld after finalStore}
    (entry : Entry instances caller active id location mapping world heap store)
    (effect : Effect instances mapping world heap store nextMap nextWorld after finalStore) :
    Entry instances caller active id location nextMap nextWorld after finalStore := by
  cases entry with
  | ordinary read descriptor =>
    obtain ⟨cell, updated, _, same⟩ := effect.metadata _ _ read
    exact .ordinary updated (same.trans descriptor)
  | generalized owner binder context located =>
    obtain ⟨located⟩ := located
    exact .generalized owner binder context (effect.retains located)

theorem At.transport {caller active mapping world heap store nextMap nextWorld after finalStore environment}
    (authority : At instances caller active mapping world heap store environment)
    (effect : Effect instances mapping world heap store nextMap nextWorld after finalStore) :
    At instances caller active nextMap nextWorld after finalStore environment := by
  induction authority with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.transport effect) ih

theorem At.lookup {caller active mapping world heap store environment id location}
    (authority : At instances caller active mapping world heap store environment)
    (lookup : Dynamic.Environment.LooksUp environment id location) :
    Entry instances caller active id location mapping world heap store := by
  induction authority with
  | nil => cases lookup
  | cons head _ ih =>
    cases lookup with
    | head => exact head
    | tail _ next => exact ih next

theorem At.generalized {caller active mapping world heap store environment id location cell function}
    (authority : At instances caller active mapping world heap store environment)
    (lookup : Dynamic.Environment.LooksUp environment id location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function) :
    ∃ binding lexical, binding.caller = caller ∧ binding.binder.id = id ∧ ContextExtension lexical active ∧
      Nonempty (Located instances function binding lexical location mapping world heap store) := by
  cases authority.lookup lookup with
  | ordinary previous empty =>
    have same := read.functional previous
    rw [same, empty] at descriptor
    cases descriptor
  | generalized owner binder context located =>
    obtain ⟨located⟩ := located
    have same := read.functional located.sourceRead
    have functionEq := Option.some.inj (descriptor.symm.trans ((congrArg Dynamic.Cell.generalized same).trans located.descriptor))
    cases functionEq
    exact ⟨_, _, owner, binder, context, ⟨located⟩⟩

/-- Real monomorphic parameter cells supply the initial lexical authority.
Deep Source heap typing rules out a principal descriptor at such a cell. -/
theorem At.of_monomorphic {caller active mapping world heap store environment scope}
    {context : SourceSemantics.Context}
    (agrees : Dynamic.EnvironmentAgrees heap scope environment)
    (typed : Dynamic.HeapWellTyped context heap)
    (monomorphic : ∀ id scheme, (id, scheme) ∈ scope → scheme.quantified = []) :
    At instances caller active mapping world heap store environment := by
  induction agrees with
  | nil => exact .nil
  | @cons scope environment id scheme location cell read _ storage tail ih =>
    have next := ih (fun child childScheme member => monomorphic child childScheme (List.mem_cons_of_mem _ member))
    cases storage with
    | ordinary _ empty => exact .cons (.ordinary read empty) next
    | generalized descriptor _ binderScheme =>
      have principal := ((typed cell read.member).generalized_inv descriptor).2.code.polymorphic
      exact False.elim (principal (binderScheme ▸ monomorphic id scheme (by simp)))

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
/-! Direct public application retains the full returned caller and heap.
The accepted execution receipt remains separate from this semantic post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Result
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)

/-- The full actual returned caller and semantic result of direct application.
Native execution is supplied separately by the accepted public checkpoint. -/
def ResultAt (context : SourceSemantics.Context) (sourceResult : TypeSystem.Ty)
    (nativeResult : Core.Ty) (outcome : Staging.Recursive.Outcome)
    (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (faults : RecursiveStageMeaning.FaultRep) : Prop :=
  RecursiveStageMeaning.ResultRepresentsFor
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld sourceResult nativeResult faults outcome value ∧
  GenericHeap.CellHeapRepresents cells
    finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    Relates caller returned ∧
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      CallableIndexedOwnedBodyRestorationAdmission.bridge context sourceResult outcome returned

variable {functions cells caller} {context : SourceSemantics.Context}
  {sourceResult : TypeSystem.Ty} {nativeResult : Core.Ty}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
  {native payload : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

/-- Actual successful decoding exposes the Source value and current heap,
including all retained captured cells and the exact native world. -/
theorem returned_value
    (result : ResultAt (registry := registry) functions cells caller context sourceResult nativeResult
      outcome after native finalStore finalMap finalWorld faults)
    (decoded : LanguageResult.decode? native = some (.succeeded payload)) :
    ∃ source, outcome = .value source ∧
      ValueRep compiled.compatible.checked registry functions finalMap finalWorld
        sourceResult source payload nativeResult ∧
      GenericHeap.CellHeapRepresents cells
        finalMap finalWorld after finalStore ∧
      finalWorld = finalStore.map Value.type ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧ StableRows returned ∧
        Dynamic.HeapWellTyped context after ∧
        Dynamic.ValueHasType context after source sourceResult := by
  obtain ⟨represented, heaps, _maps, _worlds, _administrative, _metadata,
    returned, related, post⟩ := result
  cases represented with
  | value represented =>
      simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
      subst payload
      have admission := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value post
      exact ⟨_, rfl, represented, heaps, heaps.runtime_hasTypes.world_eq,
        returned, related, admission.2.rows, admission.2.heap, admission.1⟩
  | fault represented => cases decoded
theorem ResultAt.includes
    {other : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
    (included : ∀ {cell value payload}, cells.Represents finalMap finalWorld cell value payload →
      other.Represents finalMap finalWorld cell value payload)
    (result : ResultAt (registry := registry) functions cells caller context sourceResult nativeResult
      outcome after native finalStore finalMap finalWorld faults) :
    ResultAt (registry := registry) functions other caller context sourceResult nativeResult
      outcome after native finalStore finalMap finalWorld faults :=
  ⟨result.1, result.2.1.includes included, result.2.2⟩

theorem ResultAt.ordinary_iff :
    ResultAt (registry := registry) functions
      (GenericHeap.CellModel.ordinary (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
      caller context sourceResult nativeResult outcome after native finalStore finalMap finalWorld faults ↔
    RecursivePublicApplicationResult.ResultAt (registry := registry) functions caller context sourceResult nativeResult
      outcome after native finalStore finalMap finalWorld faults := by
  simp only [ResultAt, RecursivePublicApplicationResult.ResultAt, GenericHeap.ordinaryHeap_iff,
    CompatibleAmbientHeap.HeapRepresents]
end Result

section Named
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  (arguments : List Core.Value)

def NamedResultAt (context : SourceSemantics.Context) (outcome : Staging.Recursive.Outcome)
    (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (faults : RecursiveStageMeaning.FaultRep) : Prop :=
  Evaluates (DataPatternValues.packValues arguments :: capture.captured) store
    (header.code.rename capture.embedding.lift) value finalStore ∧
  ResultAt (registry := registry) functions cells caller context header.function.resultType header.output
    outcome after value finalStore finalMap finalWorld faults

variable {functions cells owner caller header capture arguments}
  {context : SourceSemantics.Context} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
  {native payload : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

theorem named_returned_value
    (result : NamedResultAt (registry := registry) functions cells owner caller header capture arguments
      context outcome after native finalStore finalMap finalWorld faults)
    (decoded : LanguageResult.decode? native = some (.succeeded payload)) :
    ∃ source, outcome = .value source ∧
      ValueRep compiled.compatible.checked registry functions finalMap finalWorld
        header.function.resultType source payload header.output ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      finalWorld = finalStore.map Value.type ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧ StableRows returned ∧ Dynamic.HeapWellTyped context after ∧
        Dynamic.ValueHasType context after source header.function.resultType :=
  returned_value result.2 decoded

theorem NamedResultAt.ordinary_iff :
    NamedResultAt (registry := registry) functions
      (GenericHeap.CellModel.ordinary (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
      owner caller header capture arguments context outcome after native finalStore finalMap finalWorld faults ↔
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt (registry := registry)
      (payloads := arguments) functions owner caller header capture context outcome after native finalStore finalMap finalWorld faults := by
  simp only [NamedResultAt, ResultAt, CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt,
    GenericHeap.ordinaryHeap_iff, CompatibleAmbientHeap.HeapRepresents]
end Named

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicFunctionHistory
/-! Finite histories retain function exports through later completed calls.
Every new state is the returned pool of an actual semantic result, and every
new function is the corresponding public export. Captured references keep their
identity while later calls supply the current heap contents and native world. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicFunctionHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedPublicFunctionHistory (Addition Entry IssuedEntry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
  (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (receiving : SourceCoreRawMetadata.Registry)
  (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))

abbrev Caller (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :=
  State headers keys ⟨[], mapping, world, heap, store,
    SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩

variable {headers keys functions cells receiving anchor}

abbrev Result {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (owner : OwnedKey keys) (caller : Caller headers keys mapping world heap store)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (capture : NamedCapture headers owner.key header mapping world) (arguments : List Core.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) (native : Core.Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (faults : RecursiveStageMeaning.FaultRep) :=
  CellAwarePublicApplicationResult.NamedResultAt
    (registry := receiving) functions cells owner caller header capture arguments
    anchor.function.context outcome after native finalStore finalMap finalWorld faults

variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}

inductive History (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (receiving : SourceCoreRawMetadata.Registry)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram)) {artifact : Artifact} :
    (session : Session artifact) → (mapping : LocationMap) → (world : StoreTyping) →
    (heap : Dynamic.Heap) → (store : Store) → Caller headers keys mapping world heap store → List Entry → Prop where
  | first {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store}
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      {added : List Entry} {recipe : Recipe} {root : Root compiled}
      {encodedValues : SourceCoreCompatibleValues.Context}
      (sameCompiled : recipe.compiled = compiled)
      (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
        recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
      (selected : RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) headers root header)
      (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel header.function.resultType header.output outcome native added) :
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached added
  | next {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      {added : List Entry} {recipe : Recipe} {root : Root compiled}
      {encodedValues : SourceCoreCompatibleValues.Context}
      (sameCompiled : recipe.compiled = compiled)
      (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
        recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
      (selected : RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) headers root header)
      (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel header.function.resultType header.output outcome native added) :
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added)
  | first_export_error {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store}
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      {recipe : Recipe} {root : Root compiled}
      {encodedValues : SourceCoreCompatibleValues.Context}
      (sameCompiled : recipe.compiled = compiled)
      (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
        recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
      (selected : RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) headers root header)
      (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached []
  | next_export_error {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      {recipe : Recipe} {root : Root compiled}
      {encodedValues : SourceCoreCompatibleValues.Context}
      (sameCompiled : recipe.compiled = compiled)
      (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
        recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
      (selected : RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) headers root header)
      (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries
  | first_failed {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store}
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel : Nat}
      {returned : Session artifact} {reason : Core.Word}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      {recipe : Recipe} {root : Root compiled}
      {encodedValues : SourceCoreCompatibleValues.Context}
      (sameCompiled : recipe.compiled = compiled)
      (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
        recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
      (selected : RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) headers root header)
      (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached []
  | failed {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
      {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
      {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel : Nat}
      {returned : Session artifact} {reason : Core.Word}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      {recipe : Recipe} {root : Root compiled}
      {encodedValues : SourceCoreCompatibleValues.Context}
      (sameCompiled : recipe.compiled = compiled)
      (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
        recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
      (selected : RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) headers root header)
      (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
      (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
        owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
          header.function.resultType outcome reached)
      (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries
  | packed_next {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
      {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
      {sourceType : TypeSystem.Ty} {nativeType : Core.Ty} {added : List Entry}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      (started : checkpoint.HandleStart session handle argument inputFuel)
      (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
      (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
        anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context sourceType outcome reached)
      (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel sourceType nativeType outcome native added) :
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added)
  | packed_failed {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
      {argument : SourceCorePublicValues.Value} {inputFuel executionFuel : Nat}
      {returned : Session artifact} {reason : Core.Word}
      {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      (started : checkpoint.HandleStart session handle argument inputFuel)
      (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
      (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
        anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context sourceType outcome reached)
      (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries
  | packed_export_error {session : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
      {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
      {generation : SourceCorePublicValues.ExportGeneration} {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
      {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
      {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
      (started : checkpoint.HandleStart session handle argument inputFuel)
      (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
      (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
        anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
      (reached : Caller headers keys finalMap finalWorld after finalStore)
      (post : Relates caller reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context sourceType outcome reached) :
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries
  | issued {session next : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      (continued : session.IssuanceChain next) :
      History headers keys functions cells receiving anchor next mapping world heap store caller entries
  | remember_issued {session next : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry} {entry : Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      (receipt : IssuedEntry headers keys functions receiving anchor session next entry) :
      History headers keys functions cells receiving anchor next mapping world heap store caller (entries ++ [entry])
  | restored {session next : Session artifact} {mapping world heap store}
      {caller : Caller headers keys mapping world heap store} {entries : List Entry}
      (prior : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
      (restored : session.RestoredAt next) :
      History headers keys functions cells receiving anchor next mapping world heap store caller entries

def EntriesAt {artifact : Artifact} (session : Session artifact)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries,
    session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native ∧
    ValueRep compiled.compatible.checked receiving functions mapping world
      entry.sourceType entry.source entry.native entry.nativeType ∧
    Dynamic.ValueHasType anchor.function.context heap entry.source entry.sourceType

private theorem current_result {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (reached : Caller headers keys finalMap finalWorld after finalStore)
    (post : Relates caller reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
        CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
        header.function.resultType outcome reached) :
    completion.session.NativeAt finalWorld finalStore ∧
    GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
    StableRows reached ∧ Dynamic.HeapWellTyped anchor.function.context after := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
    CellAwarePublicApplicationResult.named_returned_value result decoded
  exact ⟨worldEq.symm ▸ succeeded.native_at.2, heaps, post.2.rows, typed⟩

private theorem current_export_error_result {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
    (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (reached : Caller headers keys finalMap finalWorld after finalStore)
    (post : Relates caller reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
        CallableIndexedOwnedBodyRestorationAdmission.bridge anchor.function.context
        header.function.resultType outcome reached) :
    returned.NativeAt finalWorld finalStore ∧
    GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
    StableRows reached ∧ Dynamic.HeapWellTyped anchor.function.context after := by
  obtain ⟨payload, decoded⟩ := exported.succeeded
  obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
    CellAwarePublicApplicationResult.named_returned_value result decoded
  exact ⟨worldEq.symm ▸ exported.native_at, heaps, post.2.rows, typed⟩

private theorem addition_entries {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {completion : Completion artifact} {added : List Entry}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel header.function.resultType header.output outcome native added) :
    EntriesAt (functions := functions) (receiving := receiving) (anchor := anchor)
      completion.session finalMap finalWorld after added := by
  cases addition with
  | skip => intro entry member; cases member
  | @remember source payload handle requested sourceValue nativeValue handleValue =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      rw [handleValue] at imported
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.named_returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      intro entry member
      have sameEntry := List.mem_singleton.mp member
      subst entry
      exact ⟨imported, represented, valueTyped⟩

  | @select source payload entries requested sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.named_returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
      exact RecursiveNamedPublicOutputSelections.Selected.current selection represented valueTyped encodedAt rfl payloadAt selected


  | @selectCompatible source payload entries expected requested compatible sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.named_returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
      exact RecursiveNamedPublicOutputSelections.Selected.current selection represented valueTyped encodedAt compatible payloadAt selected

  | @selectNestedCompatible source payload entries expected requested compatible sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.named_returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      exact selected.current represented valueTyped

private theorem packed_addition_entries {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {completion : Completion artifact} {added : List Entry}
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    (addition : Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel sourceType nativeType outcome native added) :
    EntriesAt (functions := functions) (receiving := receiving) (anchor := anchor)
      completion.session finalMap finalWorld after added := by
  cases addition with
  | skip => intro entry member; cases member
  | @remember source payload handle requested sourceValue nativeValue handleValue =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      rw [handleValue] at imported
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      intro entry member
      have sameEntry := List.mem_singleton.mp member
      subst entry
      exact ⟨imported, represented, valueTyped⟩
  | @select source payload entries requested sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
      exact RecursiveNamedPublicOutputSelections.Selected.current selection represented valueTyped encodedAt rfl payloadAt selected
  | @selectCompatible source payload entries expected requested compatible sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
      exact RecursiveNamedPublicOutputSelections.Selected.current selection represented valueTyped encodedAt compatible payloadAt selected

  | @selectNestedCompatible source payload entries expected requested compatible sourceValue nativeValue selection selected =>
      have decoded : LanguageResult.decode? native = some (.succeeded payload) := by rw [nativeValue]; rfl
      obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
      subst actual
      exact selected.current represented valueTyped

/-- Every retained handle is represented at the current actual caller. This
projection derives all entry laws by induction over genuine successful calls. -/
theorem History.current {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries) :
    session.NativeAt world store ∧
    GenericHeap.CellHeapRepresents cells mapping world heap store ∧
    StableRows caller ∧ Dynamic.HeapWellTyped anchor.function.context heap ∧
    EntriesAt (functions := functions) (receiving := receiving) (anchor := anchor) session mapping world heap entries := by
  induction history with
  | first sameCompiled started selected succeeded result reached post addition =>
      have actual := current_result succeeded result reached post
      exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2, addition_entries succeeded result addition⟩
  | next prior sameCompiled started selected succeeded result reached post addition ih =>
      have actual := current_result succeeded result reached post
      refine ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2, ?_⟩
      intro entry member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry old
        exact ⟨succeeded.encodes_function started.original imported,
          represented.extend (.refl _) result.2.2.2.1 result.2.2.2.2.1,
          typed.mono result.2.2.2.2.2.2.1⟩
      · exact addition_entries succeeded result addition entry added
  | first_export_error sameCompiled started selected exported result reached post =>
      have actual := current_export_error_result exported result reached post
      exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2, by intro entry member; cases member⟩
  | next_export_error prior sameCompiled started selected exported result reached post ih =>
      have actual := current_export_error_result exported result reached post
      refine ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨exported.encodes_function_from started.original.initial_registry imported,
        represented.extend (.refl _) result.2.2.2.1 result.2.2.2.2.1,
        typed.mono result.2.2.2.2.2.2.1⟩
  | first_failed sameCompiled started selected failed result reached post heapTyped =>
      have heaps := result.2.2.1
      have nativeAt : _ := heaps.runtime_hasTypes.world_eq.symm ▸ failed.native_at
      exact ⟨nativeAt, heaps, post.2.rows, heapTyped, by intro entry member; cases member⟩
  | failed prior sameCompiled started selected failed result reached post heapTyped ih =>
      have heaps := result.2.2.1
      have nativeAt : _ := heaps.runtime_hasTypes.world_eq.symm ▸ failed.native_at
      refine ⟨nativeAt, heaps, post.2.rows, heapTyped, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨failed.encodes_function started.original imported,
        represented.extend (.refl _) result.2.2.2.1 result.2.2.2.2.1,
        typed.mono result.2.2.2.2.2.2.1⟩
  | packed_next prior started succeeded result reached post addition ih =>
      obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
      obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      refine ⟨worldEq.symm ▸ succeeded.native_at.2, heaps, post.2.rows, typed, ?_⟩
      intro entry member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨imported, represented, valueTyped⟩ := ih.2.2.2.2 entry old
        exact ⟨succeeded.encodes_function_from started.initial_registry imported,
          represented.extend (.refl _) result.2.2.1 result.2.2.2.1,
          valueTyped.mono result.2.2.2.2.2.1⟩
      · exact packed_addition_entries succeeded result addition entry added
  | packed_failed prior started failed result reached post heapTyped ih =>
      have heaps := result.2.1
      have nativeAt : _ := heaps.runtime_hasTypes.world_eq.symm ▸ failed.native_at
      refine ⟨nativeAt, heaps, post.2.rows, heapTyped, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨failed.encodes_function_from started.initial_registry imported,
        represented.extend (.refl _) result.2.2.1 result.2.2.2.1,
        typed.mono result.2.2.2.2.2.1⟩
  | packed_export_error prior started exported result reached post ih =>
      obtain ⟨payload, decoded⟩ := exported.succeeded
      obtain ⟨_source, _outcome, _represented, heaps, worldEq, _returned, _related, _stable, typed, _valueTyped⟩ :=
        CellAwarePublicApplicationResult.returned_value result decoded
      refine ⟨worldEq.symm ▸ exported.native_at, heaps, post.2.rows, typed, ?_⟩
      intro entry member
      obtain ⟨imported, represented, valueTyped⟩ := ih.2.2.2.2 entry member
      exact ⟨exported.encodes_function_from started.initial_registry imported,
        represented.extend (.refl _) result.2.2.1 result.2.2.2.1,
        valueTyped.mono result.2.2.2.2.2.1⟩
  | issued prior continued ih =>
      refine ⟨continued.same_runtime.native_at ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨continued.encodes_function imported, represented, typed⟩
  | @remember_issued session next mapping world heap store caller entries entry prior receipt ih =>
      obtain ⟨same, imported, represented, typed⟩ := receipt.current caller ih.1
      refine ⟨same.native_at ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1, ?_⟩
      intro entry member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨oldImported, oldRepresented, oldTyped⟩ := ih.2.2.2.2 entry old
        exact ⟨receipt.chain.encodes_function oldImported, oldRepresented, oldTyped⟩
      · have sameEntry := List.mem_singleton.mp added
        subst entry
        exact ⟨imported, represented, typed⟩
  | restored prior restored ih =>
      refine ⟨restored.same_runtime.native_at ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1, ?_⟩
      intro entry member
      obtain ⟨imported, represented, typed⟩ := ih.2.2.2.2 entry member
      exact ⟨restored.encodes_function imported, represented, typed⟩

/-- Direct invocation of a retained handle returns the same ordered history
at its actual new session, with captures interpreted in the resulting heap. -/
theorem History.after_packed_success
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
    {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  refine ⟨reached, related, ?_⟩
  simpa only [List.append_nil] using History.packed_next history started succeeded result reached ⟨related, post⟩ Addition.skip

/-- Selected direct output functions join the existing history at the same
returned caller. The public request may erase annotations from the semantic
result; the real reimport is related by runtime type compatibility. -/
theorem History.collect_packed_success
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
    {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
    {sourceType expected : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (requested : checkpoint.ResultTypeAt expected)
    (compatible : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection sourceType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value) (added : List Entry),
      outcome = .value source ∧ native = .inRight .word payload ∧
      RecursiveNamedPublicOutputSelections.Selected selection source payload nativeType outputFuel added ∧
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added) := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  have nativeValue : native = .inRight .word payload := by
    have represented := result.1
    cases represented with
    | value represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
        subst payload
        rfl
    | fault represented => cases decoded
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
    CellAwarePublicApplicationResult.returned_value result decoded
  obtain ⟨_sourceType, encoded, encodedAt, payloadAt⟩ := succeeded.reimports_payload requested decoded
  obtain ⟨added, selected, handles, _meanings⟩ := selection.collect represented valueTyped encodedAt compatible payloadAt
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  exact ⟨reached, source, payload, added, sourceValue, nativeValue, selected, handles, related,
    .packed_next history started succeeded result reached ⟨related, post⟩
      (.selectCompatible requested compatible sourceValue nativeValue selection selected)⟩

/-- Constructor payloads and ordered mapping rows may export further functions.
Their real raw encoder and the current receiver metadata determine the exact
leaf identities before they join the existing history. -/
theorem History.collect_packed_nested_success
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe} (sameCompiled : recipe.compiled = compiled)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
    {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
    {sourceType expected : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (requested : checkpoint.ResultTypeAt expected)
    (compatible : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    {actualRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : completion.session.RegistryAt actualRegistry)
    (extension : SourceCoreRawMetadata.Extends receiving actualRegistry)
    (selection : RecursiveNamedPublicNestedOutputSelections.Selection sourceType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value) (added : List Entry),
      outcome = .value source ∧ native = .inRight .word payload ∧
      RecursiveNamedPublicNestedOutputSelections.Selected compiled.compatible.checked completion.session
        selection source payload nativeType outputFuel added ∧
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added) := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  have nativeValue : native = .inRight .word payload := by
    have represented := result.1
    cases represented with
    | value represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
        subst payload
        rfl
    | fault represented => cases decoded
  obtain ⟨source, sourceValue, represented, _heaps, _world, _returned, _related, _stable, _typed, _valueTyped⟩ :=
    CellAwarePublicApplicationResult.returned_value result decoded
  obtain ⟨_sourceType, encoded, encodedAt, payloadAt⟩ := succeeded.reimports_payload requested decoded
  have before := atRegistry.symm ▸ extension
  obtain ⟨added, selected, handles⟩ := selection.collect atRecipe
    (congrArg (fun compiled => compiled.compatible.checked) sameCompiled).symm represented
    encodedAt compatible payloadAt before
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  exact ⟨reached, source, payload, added, sourceValue, nativeValue, selected, handles, related,
    .packed_next history started succeeded result reached ⟨related, post⟩
      (.selectNestedCompatible requested compatible sourceValue nativeValue selection selected)⟩

/-- A failed direct invocation keeps all earlier handles at its returned heap.
The public semantic consumer derives heap typing from the Source fault trace. -/
theorem History.after_packed_failure
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel : Nat}
    {returned : Session artifact} {reason : Core.Word}
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  exact ⟨reached, related, .packed_failed history started failed result reached ⟨related, post⟩ heapTyped⟩

/-- A successful native call whose public export failed still retains all
previous handles and the same successful Source after-heap. -/
theorem History.after_packed_export_error
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
    {argument : SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat} {generation : ExportGeneration}
    {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (started : checkpoint.HandleStart session handle argument inputFuel)
    (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
    (result : CellAwarePublicApplicationResult.ResultAt (registry := receiving) functions cells caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2
  exact ⟨reached, related, .packed_export_error history started exported result reached ⟨related, post⟩⟩

private theorem success_shape {payload : Core.Value}
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (decoded : LanguageResult.decode? native = some (.succeeded payload)) :
    ∃ source, outcome = .value source ∧ native = .inRight .word payload := by
  cases result.2.1 with
  | value represented =>
      simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
      subst payload
      exact ⟨_, rfl, rfl⟩
  | fault represented => cases decoded

section Success
variable {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
  {publicArguments : List SourceCorePublicValues.Value} {inputFuel executionFuel outputFuel : Nat}
  {generation : SourceCorePublicValues.ExportGeneration} {completion : Completion artifact}
  {recipe : Recipe} {root : Root compiled} {encodedValues : SourceCoreCompatibleValues.Context}

/-- The first actual success establishes the current state before any exports
have been retained for later input. -/
theorem first_success
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached [] := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .first sameCompiled started selected succeeded result reached ⟨related, post⟩ .skip⟩

/-- An intervening success retains all earlier handles, including when its
own public result is ordinary data. -/
theorem History.after_success
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  refine ⟨reached, related, ?_⟩
  simpa only [List.append_nil] using History.next history sameCompiled started selected succeeded result
    reached ⟨related, post⟩ Addition.skip

/-- An initial successful native call establishes the current Source state
even when the public output cannot be exported. -/
theorem first_export_error
    {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached [] := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .first_export_error sameCompiled started selected exported result reached ⟨related, post⟩⟩

/-- A following named export error preserves the prior ordered handles at
the successful Source after-heap without registering an output handle. -/
theorem History.after_export_error
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    {returned : Session artifact} {error : SourceCoreIndexedSession.Error}
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (exported : checkpoint.ExportErrorResultAt executionFuel outputFuel generation native finalStore error returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .next_export_error history sameCompiled started selected exported result reached ⟨related, post⟩⟩

/-- The first retained function is selected from the actual successful Source
outcome and exported native payload. -/
theorem first_remembered
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {handle : SourceCorePublicValues.Handle} (handleValue : completion.value = .function handle) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value),
      outcome = .value source ∧ native = .inRight .word payload ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached [⟨header.function.resultType, source, handle, payload, header.output, outputFuel⟩] := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, nativeValue⟩ := success_shape result decoded
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, source, payload, sourceValue, nativeValue, related,
    .first sameCompiled started selected succeeded result reached ⟨related, post⟩
      (.remember requested sourceValue nativeValue handleValue)⟩

/-- Each later export appends its exact Source/native pair to the complete
ordered collection. No earlier entry is dropped or replaced. -/
theorem History.remember_success
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {handle : SourceCorePublicValues.Handle} (handleValue : completion.value = .function handle) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore)
      (source : Dynamic.Value) (payload : Core.Value),
      outcome = .value source ∧ native = .inRight .word payload ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ [⟨header.function.resultType, source, handle, payload, header.output, outputFuel⟩]) := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, nativeValue⟩ := success_shape result decoded
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, source, payload, sourceValue, nativeValue, related,
    .next history sameCompiled started selected succeeded result reached ⟨related, post⟩
      (.remember requested sourceValue nativeValue handleValue)⟩

private theorem collected_addition
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType completion.value) :
    ∃ added : List Entry, added.map Entry.handle = selection.handles ∧
      Addition (checked := compiled.compatible.checked) checkpoint completion outputFuel header.function.resultType header.output outcome native added := by
  obtain ⟨payload, decoded, _imported⟩ := succeeded.reimports
  obtain ⟨source, sourceValue, nativeValue⟩ := success_shape result decoded
  obtain ⟨_sourceType, imported⟩ := succeeded.reimports_payload requested decoded
  obtain ⟨actual, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
    CellAwarePublicApplicationResult.named_returned_value result decoded
  have same : actual = source := Staging.Recursive.Outcome.value.inj (actualOutcome.symm.trans sourceValue)
  subst actual
  obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
  obtain ⟨added, selected, handles, _meanings⟩ := selection.collect represented valueTyped encodedAt rfl payloadAt
  exact ⟨added, handles, .select requested sourceValue nativeValue selection selected⟩

/-- A first successful result can retain any selected function leaves inside
products. The original export supplies all leaf values and recursive budgets. -/
theorem first_collected
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached added := by
  obtain ⟨added, handles, addition⟩ := collected_addition requested succeeded result selection
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, added, handles, related,
    .first sameCompiled started selected succeeded result reached ⟨related, post⟩ addition⟩

/-- Collecting a product result appends all selected function leaves while
retaining earlier closures at the actual returned heap and session. -/
theorem History.collect_success
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType completion.value) :
    ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions cells receiving anchor completion.session finalMap finalWorld after finalStore
        reached (entries ++ added) := by
  obtain ⟨added, handles, addition⟩ := collected_addition requested succeeded result selection
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, added, handles, related,
    .next history sameCompiled started selected succeeded result reached ⟨related, post⟩ addition⟩

/-- A first failed call establishes an empty retained history at its actual
returned state. The public bootstrap adapter derives final heap typing. -/
theorem first_failure
    {returned : Session artifact} {reason : Core.Word}
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached [] := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .first_failed sameCompiled started selected failed result
    reached ⟨related, post⟩ heapTyped⟩

/-- A failed call retains earlier functions once Source heap preservation is
proved for its actual fault trace. Public adapters derive that condition. -/
theorem History.after_failure
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    {returned : Session artifact} {reason : Core.Word}
    (sameCompiled : recipe.compiled = compiled)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
      recipe (sameCompiled.symm ▸ root) world store arguments encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    (failed : checkpoint.FailedResultAt executionFuel native finalStore reason returned)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after) :
    ∃ reached : Caller headers keys finalMap finalWorld after finalStore,
      Relates caller reached ∧
      History headers keys functions cells receiving anchor returned finalMap finalWorld after finalStore
        reached entries := by
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached, related, .failed history sameCompiled started selected failed result
    reached ⟨related, post⟩ heapTyped⟩

end Success

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicFunctionHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
/-! Public histories retain the complete physical cache together with the same
ordinary Source exports and actual caller pool. Whole-call administrative
preservation transports this authority across every exact returned session. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CellAwarePublicFunctionHistory (Caller Result)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
  {receiving : SourceCoreRawMetadata.Registry}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}

structure History {artifact : Artifact} (session : Session artifact)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (caller : Caller headers keys mapping world heap store) (entries : List Entry) : Prop where
  semantic : CellAwarePublicFunctionHistory.History headers keys functions cells receiving anchor
    session mapping world heap store caller entries
  physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store

theorem physical_of_result
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    CallableIndexedOwnedPhysicalGlobals.Authority compiled finalMap finalStore :=
  physical.extend result.2.2.2.2.2.1

/-- The supplied history is the original public history at the actual result;
only its physical cache proof is added from whole-call preservation. -/
theorem History.after_result
    {artifact : Artifact} {session : Session artifact}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {owner : OwnedKey keys} {caller : Caller headers keys mapping world heap store} {entries : List Entry}
    (prior : History (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      session mapping world heap store caller entries)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (result : Result (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    {nextSession : Session artifact} {reached : Caller headers keys finalMap finalWorld after finalStore}
    {nextEntries : List Entry}
    (next : CellAwarePublicFunctionHistory.History headers keys functions cells receiving anchor
      nextSession finalMap finalWorld after finalStore reached nextEntries) :
    History (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      nextSession finalMap finalWorld after finalStore reached nextEntries :=
  ⟨next, physical_of_result prior.physical result⟩

/-- The stronger public caller wraps the identical reached pool. -/
def History.caller {artifact : Artifact} {session : Session artifact}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world heap store} {entries : List Entry}
    (history : History (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      session mapping world heap store caller entries) :
    CallableIndexedOwnedPhysicalState.PoolState headers keys
      ⟨[], mapping, world, heap, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩ :=
  ⟨caller, history.physical⟩

/-- The public session's actual global environment supplies the full canonical
slot layout for the next call, paired with its reached physical cache. -/
def History.canonical_caller {artifact : Artifact} {session : Session artifact}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world heap store} {entries : List Entry}
    (history : History (cells := cells) (functions := functions) (receiving := receiving) (anchor := anchor)
      session mapping world heap store caller entries) :
    (CallableIndexedOwnedPhysicalCanonicalState.protocol headers keys 0).State
      ⟨[], mapping, world, heap, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩ :=
  ⟨⟨caller, CallableIndexedOwnedPhysicalGlobals.environment_slots compiled⟩, history.physical⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeDeclarations
/-! The initial named body scope retains the original source parameter schemes.
A successful declaration lookup is authenticated against the actual inputs;
no success is invented for duplicate or qualified declarations. Native payload
types do not determine source types, and no runtime authority is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeDeclarations
open Core Frontend SourceInference
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts

/-- Exact declaration correspondence also retains polymorphic source schemes. -/
def Full (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (context : SourceSemantics.Context) : Prop :=
  ∀ binder declared index type,
    SourceCoreLocalCell.lookup? scope binder = some (index, type) →
    (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder)) = [declared] →
    Resolved.LocalScope.Lookup context.locals binder declared.scheme

private theorem identifies {source : TypedSource} {binder declared : TypedBinder}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (authentic : (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) = [declared]) : declared = binder := by
  have present : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) := List.mem_filter.mpr ⟨member, by simp⟩
  rw [authentic] at present
  exact (List.mem_singleton.mp present).symm

/-- Installing a real source binder keeps lookup correspondence even if an
unrelated declared binder would make a future compiler lookup fail. -/
theorem scope_bind {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context next : SourceSemantics.Context} {binder : TypedBinder} (payload : Core.Ty)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (declarations : Full source scope context)
    (extended : BinderExtends source.owner context binder next) :
    Full source ((binder.id, payload) :: scope) next := by
  cases extended
  intro id declared index type selected authentic
  by_cases same : binder.id = id
  · subst id
    have identified := identifies member authentic
    subst declared
    exact .head
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact .tail same (declarations _ _ _ _ previous authentic)

/-- Source-order installation and the compiler's reversed scope agree. The
native payload vector is arbitrary; only original binder identities matter. -/
theorem parameters {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context final : SourceSemantics.Context} {bindings : List (TypedBinder × Core.Ty)} {types : List TypeSystem.Ty}
    (member : ∀ binding, binding ∈ bindings → binding.1 ∈ SourceCoreDataPlaces.declaredBinders source)
    (extended : MonoBindersExtend source.owner context (bindings.map Prod.fst) types final)
    (declarations : Full source scope context) :
    Full source
      (bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope) final := by
  induction bindings generalizing context scope types with
  | nil => cases extended; exact declarations
  | cons binding rest ih =>
    cases extended with
    | cons _ head tail =>
      exact ih (fun candidate present => member candidate (List.mem_cons_of_mem _ present)) tail
        (scope_bind binding.2 (member binding List.mem_cons_self) declarations head)

private theorem reversed_scope (bindings : List (TypedBinder × Core.Ty)) (scope : SourceCoreLocalCell.Scope) :
    bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope =
      bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih => simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Every real named Header supplies its initial body's source declaration
correspondence. Residual flags, source schemes and the complete input order
are unchanged. This does not claim that every rootBinder call succeeds. -/
theorem header_scope {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} (header : Header prepared values ambient.definitions program) :
    Full header.function.source (bodyScope header) header.context := by
  have members : ∀ binding, binding ∈ header.bindings →
      binding.1 ∈ SourceCoreDataPlaces.declaredBinders header.function.source := by
    intro binding member
    have input : binding.1 ∈ header.function.source.inputs := by
      rw [header.inputs]
      exact List.mem_map.mpr ⟨binding, member, rfl⟩
    exact List.mem_append_left _ input
  have extended := header.extended
  rw [header.parameters] at extended
  have initial : Full header.function.source [] header.function.context := by
    intro _ _ _ _ selected _
    cases selected
  have final := parameters members extended initial
  simpa only [reversed_scope, List.append_nil, bodyScope] using final

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeDeclarations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
/-! Physical evidence for one actual named body. Stored generalized entries
retain their original descriptor typing and the exact shared frame reference.
This package is supplied by real parameter entry and declaration allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts CallableIndexedHistory

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function} {context : SourceSemantics.Context}

inductive Entry (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (context : SourceSemantics.Context)
    (frameLocation : Core.Location) (id : Resolved.LocalId) (location : Dynamic.Location)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop where
  | ordinary {cell : Dynamic.Cell} (read : Dynamic.Heap.Reads heap location cell)
      (descriptor : cell.generalized = none) :
      Entry compiled named context frameLocation id location mapping world heap store
  | generalized {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
      {lexical : Substitution}
      (located : Located (GeneralizedLocalInstanceValues.model compiled.indexed)
        function binding lexical location mapping world heap store)
      (owner : binding.caller = named.signature.key) (binder : binding.binder.id = id)
      (lexicalContext : ContextExtension lexical [])
      (frames : located.Frames frameLocation)
      (fields : Dynamic.RuntimeContextFields function.definitionContext context)
      (requirements : context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements) :
      Entry compiled named context frameLocation id location mapping world heap store

theorem Entry.transport {frameLocation id location mapping world heap store nextMap nextWorld after finalStore}
    (entry : Entry compiled named context frameLocation id location mapping world heap store)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store nextMap nextWorld after finalStore) :
    Entry compiled named context frameLocation id location nextMap nextWorld after finalStore := by
  cases entry with
  | ordinary read descriptor =>
    obtain ⟨cell, updated, _, same⟩ := effect.metadata _ _ read
    exact .ordinary updated (same.trans descriptor)
  | generalized located owner binder lexical frames fields requirements =>
    obtain ⟨next, same⟩ := effect.retains_values located
    exact .generalized next owner binder lexical
      (frames.transport effect.maps effect.worlds same) fields requirements

theorem Entry.authority {frameLocation id location mapping world heap store}
    (entry : Entry compiled named context frameLocation id location mapping world heap store) :
    CellAwareScopeAuthority.Entry (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] id location mapping world heap store := by
  cases entry with
  | ordinary read descriptor => exact .ordinary read descriptor
  | generalized located owner binder lexical _ _ _ => exact .generalized owner binder lexical ⟨located⟩

structure Physical (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (canonical : Core.Environment)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (environment : Dynamic.Environment) where
  native : NativeFrame
  id : Word
  selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some id
  carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    native (.named id) (some (CallableIndexedNamedGeneration.state named))
  declarations : CompatibleExpressionReads.ScopeDeclarations
    (CallableIndexedNamedGeneration.source named) scope context
  ownership : LocalIdentityOwnership (CallableIndexedNamedGeneration.source named)
  sourceDeclarations : CellAwareScopeDeclarations.Full (CallableIndexedNamedGeneration.source named) scope context
  location : Core.Location
  reference : canonical[scope.length + 1 + compiled.indexed.base.globals.length]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location)
  read : store.read? location =
    some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native)
  unmapped : location ∉ mapping
  entries : ∀ {id sourceLocation}, Dynamic.Environment.LooksUp environment id sourceLocation →
    Entry compiled named context location id sourceLocation mapping world heap store


abbrev Physical.ghost {scope canonical mapping world heap store environment}
    (physical : Physical compiled named context scope canonical mapping world heap store environment) : GhostFrame :=
  .named physical.id

def Physical.transport {scope canonical mapping world heap store environment nextMap nextWorld after finalStore}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store nextMap nextWorld after finalStore)
    (preserved : AdministrativePreserved mapping store nextMap finalStore) :
    Physical compiled named context scope canonical nextMap nextWorld after finalStore environment :=
  { native := physical.native
    id := physical.id
    selected := physical.selected
    carried := physical.carried
    declarations := physical.declarations
    ownership := physical.ownership
    sourceDeclarations := physical.sourceDeclarations
    location := physical.location
    reference := physical.reference
    read := ((preserved physical.location physical.unmapped
      (List.getElem?_eq_some_iff.mp physical.read).1).2).trans physical.read
    unmapped := (preserved physical.location physical.unmapped
      (List.getElem?_eq_some_iff.mp physical.read).1).1
    entries := fun lookup => (physical.entries lookup).transport effect }

@[simp] theorem Physical.transport_location {scope canonical mapping world heap store environment nextMap nextWorld after finalStore}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store nextMap nextWorld after finalStore)
    (preserved : AdministrativePreserved mapping store nextMap finalStore) :
    (physical.transport effect preserved).location = physical.location := rfl

@[simp] theorem Physical.transport_native {scope canonical mapping world heap store environment nextMap nextWorld after finalStore}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world heap store nextMap nextWorld after finalStore)
    (preserved : AdministrativePreserved mapping store nextMap finalStore) :
    (physical.transport effect preserved).native = physical.native := rfl

theorem Physical.generalized {scope canonical mapping world heap store environment id location cell function}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (lookup : Dynamic.Environment.LooksUp environment id location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function) :
    ∃ binding lexical, ∃ located : Located (GeneralizedLocalInstanceValues.model compiled.indexed)
        function binding lexical location mapping world heap store,
      binding.caller = named.signature.key ∧ binding.binder.id = id ∧ ContextExtension lexical [] ∧
      located.Frames physical.location ∧ Dynamic.RuntimeContextFields function.definitionContext context ∧
      context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements := by
  cases physical.entries lookup with
  | ordinary previous empty =>
    have same := read.functional previous
    rw [same, empty] at descriptor
    cases descriptor
  | generalized located owner binder lexical frames fields requirements =>
    have same := read.functional located.sourceRead
    have functionEq := Option.some.inj
      (descriptor.symm.trans ((congrArg Dynamic.Cell.generalized same).trans located.descriptor))
    cases functionEq
    exact ⟨_, _, located, owner, binder, lexical, frames, fields, requirements⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyAllocation
/-! Ordinary materialized bodies use the real marked allocator in a mixed heap.
Its constant administrative witness is constructed here; callers supply no
allocation readiness law or body execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion
open ProtectedStateTransition

private def protocol : Protocol Unit where
  State _ := Unit
  records _ := ()
  Relates _ _ := True
  refl _ := trivial
  trans _ _ := trivial

private def transport : AdministrativeTransport protocol where
  extend := fun {_} _ {_ _ _ _} _ _ _ _ => ()
  related := by intros; trivial
  records_eq := by intros; rfl

private def bindings : Bindings protocol where
  prepend _ _ _ _ := ()
  prepend_related _ _ _ _ := trivial
  prepend_records _ _ _ _ := rfl
  restore _ := ()
  restore_related _ := trivial
  restore_records _ := rfl

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells model (GeneralizedLocalDescriptorHeap.cellModel model instances))
  {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
  (sameDefinitions : layouts.definitions = definitions) (registered : frame.Registered definitions)

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

include ordinaryCells sameDefinitions registered in
theorem initialized {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (TypedLexicalControl.initializedRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (TypedLexicalControl.initializedRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {embedding : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : model.Represents mapping world binder.scheme.body sourceValue value payload)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body (some sourceValue) location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inRight .unit value]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates (value :: actual) store (annotation.expression.rename embedding.lift) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) embedding).lift
        (nextRef :: canonical) (nextRef :: value :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: value :: actual)
        (OptionalCell.referenceType payload :: payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect instances mapping world before store nextMap nextWorld after nextStore := by
  let producer := CellAllocation.of_administrative (catalog := catalog) protocol transport bindings layouts frame cells
  obtain ⟨captured, _, _, evaluated, envs, heap, localAgreement, agreement, typed, ref, read, preserved, _⟩ :=
    CellAwareOrdinaryAllocation.allocate_initialized ordinaryCells producer sameDefinitions registered
      mono extended ordinary allocation annotation same represented environments heaps locals agrees actualTyped reference read allocated () trivial
  exact ⟨captured, evaluated, envs, heap, localAgreement, agreement, typed, ref, read, preserved,
    CellAwareScopeAuthority.Effect.append _ _ (.of_allocation allocated) ⟨_,rfl⟩ ⟨_,rfl⟩⟩

include ordinaryCells sameDefinitions registered in
theorem absent {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : projects binder.scheme.body payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active
      (TypedLexicalControl.absentRequest source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (TypedLexicalControl.absentRequest source scope binder payload))
    (same : annotation.original = allocation.expression)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {embedding : Renaming} {contextLocation : Location} {native : NativeFrame} {location : Dynamic.Location}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location after) :
    ∃ captured,
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured, .inLeft payload .unit]
      let nextWorld := world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType payload) (store.length + 2)
      Evaluates actual store (annotation.expression.rename embedding) nextRef nextStore ∧
      DataHeap.EnvRepresents catalog nextMap nextWorld administrative ((binder.id, payload) :: scope)
        ((binder.id, location) :: environment) (nextRef :: canonical) definitions ∧
      GenericHeap.CellHeapRepresents cells nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after nextContext.locals ((binder.id, location) :: environment) ∧
      EnvironmentsAgree embedding.lift (nextRef :: canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType payload :: actualContext) definitions ∧
      (nextRef :: canonical)[((binder.id, payload) :: scope).length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      nextStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      CellAwareScopeAuthority.Effect instances mapping world before store nextMap nextWorld after nextStore := by
  let producer := CellAllocation.of_administrative (catalog := catalog) protocol transport bindings layouts frame cells
  obtain ⟨captured, _, _, evaluated, envs, heap, localAgreement, agreement, typed, ref, read, preserved, _⟩ :=
    CellAwareAbsentAllocation.allocate_absent ordinaryCells producer sameDefinitions registered
      mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped reference read allocated () trivial
  exact ⟨captured, evaluated, envs, heap, localAgreement, agreement, typed, ref, read, preserved,
    CellAwareScopeAuthority.Effect.append _ _ (.of_allocation allocated) ⟨_,rfl⟩ ⟨_,rfl⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectOutput
/-! A direct handle call retains its actual mixed heap and prior public history.
The original requested signature and output codec determine public completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectOutput
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header)
open CellAwarePublicFunctionHistory (Caller)
open CellAwarePublicApplicationResult (ResultAt)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  {parameter requested sourceResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
  {callable packed : Core.Value}
  (started : StartAt session handle argument inputFuel checkpoint recipe world store
    parameter requested nativeParameter nativeResult callable packed encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (resultView : SourceCoreRawMetadata.runtimeType requested = SourceCoreRawMetadata.runtimeType sourceResult)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {source : Dynamic.Value} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : ResultAt (registry := registry) functions cells caller anchor.function.context sourceResult nativeResult
    (.value source) after native finalStore finalMap finalWorld faults)
  {requiredExecution : Nat}
  (completes : ∀ executionFuel, requiredExecution ≤ executionFuel → checkpoint.NativeDone executionFuel native finalStore)

include started exactRegistry resultView ready atCheckpoint result completes in
theorem exports :
    ∃ payload requiredOutput,
      native = .inRight .word payload ∧
      ValueRep recipe.compiled.compatible.checked registry functions finalMap finalWorld
        sourceResult source payload nativeResult ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ actual.session.ExportsReady := by
  obtain ⟨payload, same⟩ : ∃ payload, native = .inRight .word payload := by
    cases result.1 with
    | value _ => exact ⟨_, rfl⟩
  subst native
  have represented : ValueRep recipe.compiled.compatible.checked registry functions finalMap finalWorld
      sourceResult source payload nativeResult := by
    cases result.1 with
    | value represented => exact represented
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions requested payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output represented
    rw [exactRegistry, result.2.1.runtime_hasTypes.world_eq] at shaped
    exact .compatible resultView shaped
  have checkpointRegistry : checkpoint.RegistryAt encodedValues.registry := by
    have values := started.values
    cases checkpoint
    change _ = encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have checkpointReady := started.original.initial_registry.exportsReady ready
  obtain ⟨requiredOutput, exported⟩ := publicCheckpoint.output_succeeded_uniform
    atCheckpoint started.recipe_eq checkpointRegistry checkpointReady started.requested shape
  exact ⟨payload, requiredOutput, rfl, represented, fun executionFuel outputFuel outcome enough outputEnough resumed =>
    exported executionFuel (completes executionFuel enough) outputFuel outputEnough outcome resumed⟩

include started exactRegistry resultView ready atCheckpoint result completes in
/-- The actual successful direct call keeps all earlier handles and the full
physical cache at its restored caller and final mixed heap. -/
theorem after_success {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨_payload, requiredOutput, _nativeEq, _represented, exported⟩ :=
    exports functions cells started exactRegistry resultView ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_packed_success started.original actualResult result
  exact ⟨completion, actual, generation, reached, succeeded, actualResult, actualAt, related,
    ⟨retained, history.physical.extend result.2.2.2.2.1⟩,
    exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectOutput
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysicalExtension
/-! Real monomorphic parameters initialize the named physical scope. Each
subsequent lexical declaration extends only the original binder context and
retains the same selected frame and caller key. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts CallableIndexedHistory

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function} {context nextContext : SourceSemantics.Context}

theorem Entry.recontext {frameLocation id location mapping world heap store binder}
    {sourceOwner : Resolved.DeclarationId}
    (entry : Entry compiled named context frameLocation id location mapping world heap store)
    (extended : BinderExtends sourceOwner context binder nextContext)
    (different : binder.id ≠ id) :
    Entry compiled named nextContext frameLocation id location mapping world heap store := by
  cases entry with
  | ordinary read descriptor => exact .ordinary read descriptor
  | generalized located owner binderId lexical frames fields requirements =>
    refine .generalized located owner binderId lexical frames
      (fields.trans (.ofBinderExtends extended)) ?_
    cases extended
    exact .tail (by simpa only [located.attachment.binder, binderId] using different) requirements

private theorem monomorphic_entries {frameLocation mapping world heap store environment scope}
    (agrees : Dynamic.EnvironmentAgrees heap scope environment)
    (typed : Dynamic.HeapWellTyped context heap)
    (monomorphic : ∀ id scheme, (id, scheme) ∈ scope → scheme.quantified = []) :
    ∀ {id location}, Dynamic.Environment.LooksUp environment id location →
      Entry compiled named context frameLocation id location mapping world heap store := by
  induction agrees with
  | nil => intro id location lookup; cases lookup
  | @cons scope environment headId scheme headLocation cell read _ storage tail ih =>
    intro id location lookup
    cases lookup with
    | head =>
      cases storage with
      | ordinary _ empty => exact .ordinary read empty
      | generalized descriptor _ binderScheme =>
        have principal := ((typed cell read.member).generalized_inv descriptor).2.code.polymorphic
        exact False.elim (principal (binderScheme ▸ monomorphic headId scheme (by simp)))
    | tail _ next =>
      exact ih (fun child childScheme member => monomorphic child childScheme (List.mem_cons_of_mem _ member)) next

def Physical.of_monomorphic {scope canonical mapping world heap store environment}
    (native : NativeFrame) (id : Word)
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some id)
    (carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      native (.named id) (some (CallableIndexedNamedGeneration.state named)))
    (declarations : CompatibleExpressionReads.ScopeDeclarations (CallableIndexedNamedGeneration.source named) scope context)
    (ownership : LocalIdentityOwnership (CallableIndexedNamedGeneration.source named))
    (sourceDeclarations : CellAwareScopeDeclarations.Full (CallableIndexedNamedGeneration.source named) scope context)
    (location : Core.Location)
    (reference : canonical[scope.length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : store.read? location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : location ∉ mapping)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (typed : Dynamic.HeapWellTyped context heap)
    (monomorphic : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    Physical compiled named context scope canonical mapping world heap store environment :=
  ⟨native, id, selected, carried, declarations, ownership, sourceDeclarations, location, reference, read, unmapped,
    monomorphic_entries locals typed monomorphic⟩

def Physical.cons {scope canonical mapping world heap store environment binder payload sourceLocation}
    (physical : Physical compiled named context scope canonical mapping world heap store environment)
    (extended : BinderExtends (CallableIndexedNamedGeneration.source named).owner context binder nextContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (CallableIndexedNamedGeneration.source named)
      ((binder.id, payload) :: scope) nextContext)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders (CallableIndexedNamedGeneration.source named))
    (reference : Core.Value)
    (head : Entry compiled named nextContext physical.location binder.id sourceLocation mapping world heap store) :
    Physical compiled named nextContext ((binder.id, payload) :: scope) (reference :: canonical)
      mapping world heap store ((binder.id, sourceLocation) :: environment) := by
  refine ⟨physical.native, physical.id, physical.selected, physical.carried, declarations, physical.ownership,
    CellAwareScopeDeclarations.scope_bind payload member physical.sourceDeclarations extended, physical.location, ?_, physical.read, physical.unmapped, ?_⟩
  · change (reference :: canonical)[scope.length + 1 + 1 + compiled.indexed.base.globals.length]? = _
    rw [show scope.length + 1 + 1 + compiled.indexed.base.globals.length =
      (scope.length + 1 + compiled.indexed.base.globals.length) + 1 by omega]
    exact physical.reference
  · intro id location lookup
    cases lookup with
    | head => exact head
    | tail different previous => exact (physical.entries previous).recontext extended different

end Solcore.SourceSemantics.CoreLowering.CellAwareScopePhysical
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput
/-! Successful named execution derives public output fuel from its represented
value. The exact returned session retains mixed cells, physical cache authority,
and all earlier exported function values. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CellAwarePublicFunctionHistory (Caller Result)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world before store}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {root : Root recipe.compiled}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
    (program := Program.ofChecked recipe.compiled.sourceProgram) headers root header)
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
    recipe root world store arguments encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {source : Dynamic.Value} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : Result (cells := cells) (functions := functions) (receiving := registry) (anchor := anchor)
    owner caller header capture arguments (.value source) after native finalStore finalMap finalWorld faults)
  {requiredExecution : Nat}
  (completes : ∀ executionFuel, requiredExecution ≤ executionFuel → checkpoint.NativeDone executionFuel native finalStore)

include selected started exactRegistry ready atCheckpoint result completes in
theorem exports :
    ∃ payload requiredOutput,
      native = .inRight .word payload ∧
      ValueRep recipe.compiled.compatible.checked registry functions finalMap finalWorld
        header.function.resultType source payload header.output ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ actual.session.ExportsReady := by
  obtain ⟨payload, same⟩ : ∃ payload, native = .inRight .word payload := by
    have represented := result.2.1
    cases represented with
    | value _ => exact ⟨_, rfl⟩
  subst native
  have represented : ValueRep recipe.compiled.compatible.checked registry functions finalMap finalWorld
      header.function.resultType source payload header.output := by
    have related := result.2.1
    cases related with
    | value represented => exact represented
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output represented
    rw [exactRegistry, result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : checkpoint.RegistryAt encodedValues.registry := by
    have values := started.values
    cases checkpoint
    change _ = encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType] at requested
  have checkpointReady := started.original.initial_registry.exportsReady ready
  obtain ⟨requiredOutput, exported⟩ := publicCheckpoint.output_succeeded_uniform
    atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  exact ⟨payload, requiredOutput, rfl, represented, fun executionFuel outputFuel outcome enough outputEnough resumed =>
    exported executionFuel (completes executionFuel enough) outputFuel outputEnough outcome resumed⟩

include selected started exactRegistry ready atCheckpoint result completes in
/-- A first successful public call produces a reusable physical history at
the actual returned mixed heap; no output success is assumed. -/
theorem first_success
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
    ∃ requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached [] ∧
          actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨_payload, requiredOutput, _nativeEq, _represented, exported⟩ :=
    exports functions cells selected started exactRegistry ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨reached, related, history⟩ := CellAwarePublicFunctionHistory.first_success
    rfl started selected actualResult result
  have retained : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) actual.session finalMap finalWorld after finalStore reached [] :=
    ⟨history, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩
  exact ⟨completion, actual, generation, reached, succeeded, actualResult, actualAt, related,
    retained, exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady⟩

include selected started exactRegistry ready atCheckpoint result completes in
/-- Following calls preserve earlier handle entries at the exact public
return and retain the full physical cache after all body effects. -/
theorem after_success {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨_payload, requiredOutput, _nativeEq, _represented, exported⟩ :=
    exports functions cells selected started exactRegistry ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_success rfl started selected actualResult result
  exact ⟨completion, actual, generation, reached, succeeded, actualResult, actualAt, related,
    history.after_result result retained, exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedOutput
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicResultContext
/-! Public continuation contexts are supported by actual Source typing. The
returned heap, native evaluation and owned state are kept exactly. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  {caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩}
  {first second : SourceSemantics.Context} {sourceType : TypeSystem.Ty} {nativeType : Ty}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {value : Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}

theorem ResultAt.context
    (supports : Dynamic.TypeContextSupports first second)
    (result : ResultAt (registry := registry) functions cells caller first sourceType nativeType
      outcome after value finalStore finalMap finalWorld faults) :
    ResultAt (registry := registry) functions cells caller second sourceType nativeType
      outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨represented, heaps, maps, worlds, administrative, metadata, returned, related, post⟩ := result
  refine ⟨represented, heaps, maps, worlds, administrative, metadata, returned, related, ?_⟩
  cases outcome with
  | value source =>
    refine ⟨post.rows, ?_⟩
    intro source same
    obtain ⟨typed, heapTyped⟩ := post.successful source same
    exact ⟨typed.transportContext supports, heapTyped.transportContext supports⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨post.rows, by intro source same; cases same⟩
    | stage origin call reason => exact post

theorem NamedResultAt.context
    {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Value}
    (supports : Dynamic.TypeContextSupports first second)
    (result : NamedResultAt (registry := registry) functions cells owner caller header capture arguments
      first outcome after value finalStore finalMap finalWorld faults) :
    NamedResultAt (registry := registry) functions cells owner caller header capture arguments
      second outcome after value finalStore finalMap finalWorld faults :=
  ⟨result.1, result.2.context supports⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicCells
/-! The actual receiver may extend raw metadata while retaining the same
ordinary values and generalized descriptors at their original locations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicCells
open Core Frontend GeneralHeap CompatiblePayload

abbrev Family (definitions : DataEnvironment) :=
  SourceCoreRawMetadata.Registry → GenericHeap.CellModel definitions

/-- This law only transports cell representation along a forward metadata
extension. It does not supply expression, body or invocation semantics. -/
def ExtendsRegistry {definitions : DataEnvironment} (cells : Family definitions) : Prop :=
  ∀ {registry future}, SourceCoreRawMetadata.Extends registry future →
    ∀ {mapping world cell value payload},
      (cells registry).Represents mapping world cell value payload →
      (cells future).Represents mapping world cell value payload

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}

def generalized (functions : FunctionModel checked.catalog ambient)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) :
    Family ambient.definitions :=
  fun registry => GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel checked registry functions) instances

theorem generalized_extends_registry
    (functions : FunctionModel checked.catalog ambient)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions) :
    ExtendsRegistry (generalized functions instances) := by
  intro registry future extension mapping world cell value payload represented
  cases represented with
  | ordinary prior => exact .ordinary (CompatibleHeap.cell_extend_registry prior extension)
  | generalized stored => exact .generalized stored

/-- Initial ordinary cells embed at the same Source/native heap. There is no
conversion in the reverse direction for a heap containing descriptors. -/
theorem generalized_initial
    {functions : FunctionModel checked.catalog ambient}
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store}
    (related : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store) :
    GenericHeap.CellHeapRepresents (generalized functions instances registry) mapping world heap store :=
  GeneralizedLocalDescriptorHeap.initial related

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicCells
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicHistoryInitial
/-! A real ordinary public history embeds into the mixed cell representation
without changing a call, capture, heap, session or ordered export. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicHistoryInitial
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open RecursiveNamedPublicFunctionHistory (Caller Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  (instances : GeneralizedLocalDescriptorHeap.InstanceModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}

private theorem named_result
    {owner : OwnedKey keys} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value}
    {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (result : RecursiveNamedPublicFunctionHistory.Result (functions := functions) (receiving := registry) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults) :
    CellAwarePublicFunctionHistory.Result (functions := functions) (receiving := registry) (anchor := anchor)
      (cells := CellAwarePublicCells.generalized functions instances registry)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults :=
  ⟨result.1, result.2.1, CellAwarePublicCells.generalized_initial instances result.2.2.1, result.2.2.2⟩

private theorem packed_result
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value}
    {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
    (result : RecursivePublicApplicationResult.ResultAt (registry := registry) functions caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults) :
    CellAwarePublicApplicationResult.ResultAt (registry := registry) functions
      (CellAwarePublicCells.generalized functions instances registry) caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults :=
  ⟨result.1, CellAwarePublicCells.generalized_initial instances result.2.1, result.2.2⟩

/-- Every transition still carries its original start and completion receipt.
Only ordinary cell representation is injected into the descriptor-aware model. -/
theorem of_ordinary {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : RecursiveNamedPublicFunctionHistory.History headers keys functions registry anchor
      session mapping world heap store caller entries) :
    CellAwarePublicFunctionHistory.History headers keys functions
      (CellAwarePublicCells.generalized functions instances registry) registry anchor
      session mapping world heap store caller entries := by
  induction history with
  | first sameCompiled started selected succeeded result reached post addition =>
      exact .first sameCompiled started selected succeeded (named_result instances result) reached post addition
  | next prior sameCompiled started selected succeeded result reached post addition ih =>
      exact .next ih sameCompiled started selected succeeded (named_result instances result) reached post addition
  | first_export_error sameCompiled started selected exported result reached post =>
      exact .first_export_error sameCompiled started selected exported (named_result instances result) reached post
  | next_export_error prior sameCompiled started selected exported result reached post ih =>
      exact .next_export_error ih sameCompiled started selected exported (named_result instances result) reached post
  | first_failed sameCompiled started selected failed result reached post heapTyped =>
      exact .first_failed sameCompiled started selected failed (named_result instances result) reached post heapTyped
  | failed prior sameCompiled started selected failed result reached post heapTyped ih =>
      exact .failed ih sameCompiled started selected failed (named_result instances result) reached post heapTyped
  | packed_next prior started succeeded result reached post addition ih =>
      exact .packed_next ih started succeeded (packed_result instances result) reached post addition
  | packed_failed prior started failed result reached post heapTyped ih =>
      exact .packed_failed ih started failed (packed_result instances result) reached post heapTyped
  | packed_export_error prior started exported result reached post ih =>
      exact .packed_export_error ih started exported (packed_result instances result) reached post
  | issued prior continued ih => exact .issued ih continued
  | remember_issued prior receipt ih => exact .remember_issued ih receipt
  | restored prior restored ih => exact .restored ih restored

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicHistoryInitial
end
