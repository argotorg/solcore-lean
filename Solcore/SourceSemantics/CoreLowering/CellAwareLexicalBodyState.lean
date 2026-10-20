import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyScopedDeterminacy
import Solcore.SourceSemantics.CoreLowering.CellAwareReadProductCompletion
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodyAllocation
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes

/-! Actual lexical entries for ordinary bodies inside mixed closure heaps.
The state records the current physical frame and reached Source heap. Scoped
continuations may restore bindings while retaining every real allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory

inductive Outcome where
  | returned (value : Dynamic.Value)
  | fallthrough (environment : Dynamic.Environment)
  | fault (reason : Dynamic.SemanticFault)

def Outcome.embed : Outcome → Staging.Recursive.BodyOutcome
  | .returned value => .returned value
  | .fallthrough environment => .fallthrough environment
  | .fault reason => .fault (.semantic reason)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  (rawRegistry : SourceCoreRawMetadata.Registry)
  (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions)
  (program : Program) (invocation : Staging.Recursive.Scope)
  (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)

local notation "model" => CompatibleAmbientHeap.payloadModel checked rawRegistry functions
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel model instances

structure Entry (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) where
  mapping : LocationMap
  world : StoreTyping
  administrative : Core.Context
  actualContext : Core.Context
  environment : Dynamic.Environment
  canonical : Environment
  actual : Environment
  heap : Dynamic.Heap
  store : Store
  embedding : Renaming
  location : Location
  native : NativeFrame
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
    mapping world administrative scope environment canonical ambient.definitions
  heaps : GenericHeap.CellHeapRepresents cells mapping world heap store
  heapTyped : Dynamic.HeapWellTyped context heap
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  agrees : EnvironmentsAgree embedding canonical actual
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions
  reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type location)
  read : store.read? location = some (SourceCoreCallableIndexedFrames.encode frame native)
  unmapped : location ∉ mapping
  runtime : Dynamic.SourceRuntimeValid program context invocation.source
  covers : invocation.evidence.Covers context

variable {functions rawRegistry instances program invocation frame globals}

def Entry.advance {context scope}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (preserved : AdministrativePreserved entry.mapping entry.store mapping store)
    (effect : CellAwareScopeAuthority.Effect instances entry.mapping entry.world entry.heap entry.store mapping world heap store) :
    Entry functions rawRegistry instances program invocation frame globals context scope where
  mapping := mapping
  world := world
  administrative := entry.administrative
  actualContext := entry.actualContext
  environment := entry.environment
  canonical := entry.canonical
  actual := entry.actual
  heap := heap
  store := store
  embedding := entry.embedding
  location := entry.location
  native := entry.native
  environments := entry.environments.extend effect.maps effect.worlds
  heaps := heaps
  heapTyped := heapTyped
  locals := entry.locals.mono effect.metadata
  agrees := entry.agrees
  actualTyped := entry.actualTyped.weaken effect.worlds
  reference := entry.reference
  read := (preserved entry.location entry.unmapped (List.getElem?_eq_some_iff.mp entry.read).1).2.trans entry.read
  unmapped := (preserved entry.location entry.unmapped (List.getElem?_eq_some_iff.mp entry.read).1).1
  runtime := entry.runtime
  covers := entry.covers

def Entry.prefix {context scope}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (value : Value) (type : Ty) (typed : RuntimeValueHasType entry.world value type ambient.definitions) :
    Entry functions rawRegistry instances program invocation frame globals context scope :=
  { entry with
    actualContext := type :: entry.actualContext
    actual := value :: entry.actual
    embedding := Renaming.comp (Renaming.insertion 0) entry.embedding
    agrees := GenericExpressionMeaning.agree_prefix entry.agrees value
    actualTyped := .cons typed entry.actualTyped }

structure Result {context scope}
    (entry : Entry functions rawRegistry instances program invocation frame globals context scope)
    (registry : Staging.Recursive.Registry) (faults : RecursiveStageMeaning.FaultRep)
    (mode : Bool) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) where
  size : Nat
  finalContext : SourceSemantics.Context
  outcome : Outcome
  after : Dynamic.Heap
  value : Value
  store : Store
  mapping : LocationMap
  world : StoreTyping
  trace : Staging.Recursive.Size.StatementsIn program registry mode size invocation context entry.environment entry.heap
    statements finalContext outcome.embed after
  evaluated : Evaluates entry.actual entry.store (code.rename entry.embedding) value store
  represented : CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents model mapping world mode expected type faults outcome.embed value
  heaps : GenericHeap.CellHeapRepresents cells mapping world after store
  preserved : AdministrativePreserved entry.mapping entry.store mapping store
  effect : CellAwareScopeAuthority.Effect instances entry.mapping entry.world entry.heap entry.store mapping world after store
  fallthroughTyped : ∀ environment, outcome = .fallthrough environment → Dynamic.HeapWellTyped context after

  determines : CellAwareLexicalBodyDeterminacy.Body (program := program) (registry := registry) (invocation := invocation)
    mode context entry.environment entry.heap statements finalContext outcome.embed after

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyState
