import Solcore.SourceSemantics.CoreLowering.GenericForHeaderReflection
import Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionBindings
import Solcore.SourceSemantics.CoreLowering.ProtectedForBodyContracts

/-! Static header trees are shared with the generic grammar. A dynamic stopping
receipt pairs its actual typed prefix with the protected installed observations.
The receipt contains no meaning or execution of its syntactic continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Fallthrough)
abbrev Tree := GenericForHeader.Tree
abbrev Scope := GenericForHeader.Scope
abbrev ValuesContext := GenericForHeader.ValuesContext

structure TailFor (validity : SourceSemantics.Context → Prop) {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame)
    (continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    extends TypedForHeader.TailFor validity registry functions source solved evidence administrative frame globals
      contextLocation native continuation context environment heap where
  installed : entry scope mapping world heap store canonical

abbrev Tail {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame)
    (continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) :=
  TailFor (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation context environment heap

inductive ResultFor (validity : SourceSemantics.Context → Prop) {entry : ProtectedExpressionMeaning.Entry} {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame) (type : Ty) (faults : FunctionCalls.FaultRep)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (mapping : LocationMap) (world : StoreTyping) (store : Store)
    (value : Value) (finalStore : Store) : Prop where
  | continues {finalContext finalEnvironment after}
      (tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after)
      (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after)
      (maps : LocationMap.Extends mapping tail.mapping) (worlds : WorldExtends world tail.world)
      (preservation : AdministrativePreserved mapping store tail.mapping tail.store)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (remaining : Evaluates tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
      ResultFor validity (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
        context environment before items mapping world store value finalStore
  | fault {finalContext reason token after finalMap finalWorld}
      (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after)
      (same : value = .inLeft (LocalLoop.controlType type) (.word token)) (matched : faults reason token)
      (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (preservation : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after) :
      ResultFor validity (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
        context environment before items mapping world store value finalStore

abbrev Result {entry : ProtectedExpressionMeaning.Entry} {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame) (type : Ty) (faults : FunctionCalls.FaultRep)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (mapping : LocationMap) (world : StoreTyping) (store : Store)
    (value : Value) (finalStore : Store) : Prop :=
  ResultFor (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
    context environment before items mapping world store value finalStore


theorem binder_context_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

variable {entry : ProtectedExpressionMeaning.Entry} {values : GenericForHeader.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {registry : SourceCoreRawMetadata.Registry} {type : Ty} {faults : FunctionCalls.FaultRep}
  {continuation : SourceSemantics.Context → SourceCoreLocalCell.Scope → Expr → Prop}

theorem ResultFor.prepend {validity : SourceSemantics.Context → Prop} {context middleContext : SourceSemantics.Context}
    {environment nextEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm}
    {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {store middleStore finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (head : Dynamic.ForItemExecutes program context evidence source environment before item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (preservation : AdministrativePreserved mapping store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend before middle)
    (tail : ResultFor validity (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      middleContext nextEnvironment middle items nextMap nextWorld middleStore value finalStore) :
    ResultFor validity (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before (item :: items) mapping world store value finalStore := by
  cases tail with
  | continues tail trace lastMaps lastWorlds lastFrame lastMetadata remaining =>
    exact .continues tail (.cons head trace) (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) remaining
  | fault trace same matched heaps lastMaps lastWorlds lastFrame lastMetadata =>
    exact .fault (.tail head trace) same matched heaps (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata)


theorem Result.prepend {context middleContext : SourceSemantics.Context}
    {environment nextEnvironment : Dynamic.Environment} {before middle : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm}
    {mapping nextMap : LocationMap} {world nextWorld : StoreTyping} {store middleStore finalStore : Store}
    {contextLocation : Location} {native : NativeFrame} {value : Value}
    (head : Dynamic.ForItemExecutes program context evidence source environment before item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (preservation : AdministrativePreserved mapping store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend before middle)
    (tail : Result (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      middleContext nextEnvironment middle items nextMap nextWorld middleStore value finalStore) :
    Result (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before (item :: items) mapping world store value finalStore := by
  exact ResultFor.prepend head maps worlds preservation metadata tail


end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
