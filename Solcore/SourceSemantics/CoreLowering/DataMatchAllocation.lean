import Solcore.SourceSemantics.CoreLowering.DataEnvironment
import Solcore.SourceSemantics.CoreLowering.DataMatchDecision

/-! Source-ordered allocation of authenticated match binders into the new data
heap/environment relation. This allocation theorem constructs the independent
source BindersAllocate derivation. It does not assume execution of a selected
arm or claim that the entire generated match statement is already preserved. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchAllocation
open Core Frontend Frontend.SourceInference GeneralHeap DataHeap
open SourceCoreDataMatches DataPatternBindings

/-- The compiled binder order is exactly the independently matched binder
order, including retained binder metadata. -/
theorem BindingsRep.binders {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values) :
    bindings.map Prod.fst = sources.map Prod.fst := by
  induction represented with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg (List.cons _) ih

/-- Bindings allocate in source order, while lexical environments put each new
reference at the front. Source/Core locations use their independent heap/store
lengths; existing administrative code remains unchanged throughout. -/
theorem BindingsRep.allocate {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {bindings : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep catalog signatures bindings sources values)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {scope : Scope} {environment : Dynamic.Environment} {canonical : Environment}
    {heap : Dynamic.Heap} {store : Store}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical)
    (heaps : DataHeap.HeapRepresents catalog signatures mapping world heap store) :
    ∃ finalEnvironment finalHeap finalCanonical finalStore finalMap finalWorld,
      Dynamic.BindersAllocate environment heap (sources.map Prod.fst) (sources.map Prod.snd)
        finalEnvironment finalHeap ∧
      DataHeap.EnvRepresents catalog finalMap finalWorld administrativeContext
        (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope)
        finalEnvironment finalCanonical ∧
      DataHeap.HeapRepresents catalog signatures finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  induction represented generalizing mapping world scope environment canonical heap store with
  | nil =>
    exact ⟨environment, heap, canonical, store, mapping, world, .nil _ _, environments, heaps,
      .refl _, .refl _, .refl _ _⟩
  | @cons binder type sourceValue value bindings sources values projection head tail ih =>
    obtain ⟨nextEnvironment, nextHeaps⟩ := environments.bind heaps (.initialized projection head)
      (Dynamic.Heap.Allocates.append (type := binder.scheme.body) (value := some sourceValue))
    obtain ⟨finalEnvironment, finalHeap, finalCanonical, finalStore, finalMap, finalWorld,
      allocated, finalEnvironmentRep, finalHeapRep, moreMaps, moreWorlds, moreFrame⟩ :=
      ih nextEnvironment nextHeaps
    exact ⟨finalEnvironment, finalHeap, finalCanonical, finalStore, finalMap, finalWorld,
      .cons .append allocated, finalEnvironmentRep, finalHeapRep,
      (show LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans moreMaps,
      (show WorldExtends world (world ++ [OptionalCell.cellType type]) from ⟨_, rfl⟩).trans moreWorlds,
      (AdministrativePreserved.allocate mapping store (.inRight .unit value)).trans moreFrame⟩

end Solcore.SourceSemantics.CoreLowering.DataMatchAllocation
