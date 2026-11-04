import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical

/-!
# Protected contracts: statements on the state

Lexical, `while`, `for` and match statements on the protected state: control, edges, readiness and contracts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateWhile
/-! The live loop activation and its actual protected state have separate
fields. Child transitions retain their reached state; installing the hidden
self cell is an administrative operation with an unchanged record observation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.While
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext LoopState Progress installedStore installedWorld)
universe u v
variable {Records : Type v}

structure State (protocol : Protocol.{u, v} Records)
    (values : ValuesContext) {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (context : SourceSemantics.Context) (scope : Scope) (administrative actualContext : Core.Context)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (contextLocation location : Location) (type : Ty) (condition body : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  live : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
    contextLocation location type condition body reason mapping world heap store
  retained : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩

variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {contextLocation location : Location} {type : Ty} {condition body : Expr} {reason : Word}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {before after : Dynamic.Heap} {store futureStore : Store}
  {Records : Type v} {protocol : Protocol.{u, v} Records}

/-- Keep the actual child post-witness while transporting the live loop frame. -/
theorem State.reach
    (state : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body reason mapping world before store)
    (progress : Progress values registry functions before after mapping futureMap world futureWorld store futureStore)
    (transition : Transition protocol state.retained
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩) :
    ∃ reached : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body reason futureMap futureWorld after futureStore,
      protocol.Relates state.retained reached.retained := by
  obtain ⟨final, related⟩ := transition
  exact ⟨⟨state.live.progress progress, final⟩, related⟩

/-- Install the real self cell, retaining the exact input records. -/
def install (transport : AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (typed : HasType actualContext (LocalLoop.whileLoop type condition body reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type condition body reason mapping
      (installedWorld world type) before
      (installedStore store type condition body (LocalLoop.fallthrough type) reason actual) := by
  have facts := TypedLexicalWhile.install reason heaps actualTyped typed
  refine ⟨?_, transport.extend initial (.refl mapping) facts.2.1 facts.2.2.2.2.2
    (Dynamic.HeapMetadataExtend.refl before)⟩
  obtain ⟨finalHeaps, worlds, selfUnmapped, selfTyped, selfRead, preserved⟩ := facts
  obtain ⟨contextUnmapped, contextRead⟩ := TypedLexicalWhile.retain unmapped read preserved
  exact ⟨environments.extend (.refl mapping) worlds, finalHeaps, locals, actualTyped.weaken worlds,
    ⟨native, contextRead⟩, contextUnmapped, selfTyped, selfRead, selfUnmapped⟩


theorem install_related (transport : AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (typed : HasType actualContext (LocalLoop.whileLoop type condition body reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    protocol.Relates initial (install transport environments heaps locals actualTyped typed read unmapped initial).retained := by
  dsimp only [install]
  apply transport.related

theorem install_records (transport : AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (typed : HasType actualContext (LocalLoop.whileLoop type condition body reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    protocol.records (install transport environments heaps locals actualTyped typed read unmapped initial).retained = protocol.records initial := by
  dsimp only [install]
  apply transport.records_eq

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.While
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateLexical
/-! Five-way lexical flow carries its actual protected post-witness. The
existing stopping lexical evidence remains intact; each result normalizes the
state index to the producer's entry scope and canonical environment. These are
pointwise contracts and compatibility adapters, with no execution induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.Lexical
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (LexicalResult)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open RecursiveNamedLoopContracts (ExecutesAt)
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}

def PreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_trace : ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def ReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

/-- Forget only the concrete transition suffix. -/
theorem PreservesAtFor.forget {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : PreservesAtFor protocol functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.PreservesAtFor functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (entry := entry protocol) (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped installed trace
  obtain ⟨initial⟩ := installed
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

theorem ReflectsAtFor.forget {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ReflectsAtFor protocol functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (entry := entry protocol) (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped installed evaluated
  obtain ⟨initial⟩ := installed
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

/-- This compatibility lift keeps the input's complete record observation.
Record-producing flow must supply its direct transition instead. -/
theorem PreservesAtFor.of_administrative (transport : AdministrativeTransport protocol)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (entry := entry protocol) (scope := scope) mode statements expected type code) :
    PreservesAtFor protocol functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped ⟨initial⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    AdministrativeTransport.transition protocol transport initial maps worlds frame metadata⟩

theorem ReflectsAtFor.of_administrative (transport : AdministrativeTransport protocol)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (entry := entry protocol) (scope := scope) mode statements expected type code) :
    ReflectsAtFor protocol functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped ⟨initial⟩ evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    AdministrativeTransport.transition protocol transport initial maps worlds frame metadata⟩

/-- Legacy callers retain their original guarded proposition. -/
def legacyProtocol (guarded : ProtectedExpressionMeaning.Entry) : Protocol Unit where
  State index := PLift (guarded index.scope index.mapping index.world index.heap index.store index.canonical)
  records _ := ()
  Relates _ _ := True
  refl _ := trivial
  trans _ _ := trivial

def legacyTransport {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded) :
    AdministrativeTransport (legacyProtocol guarded) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    ⟨transport.extend state.down maps worlds frame metadata⟩
  related := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => trivial
  records_eq := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => rfl

/-- Preserve the legacy entry only through its actual proved effects. -/
theorem legacy_preserves {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (entry := guarded) (scope := scope) mode statements expected type code) :
    PreservesAtFor (legacyProtocol guarded) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

theorem legacy_reflects {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (entry := guarded) (scope := scope) mode statements expected type code) :
    ReflectsAtFor (legacyProtocol guarded) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial.down evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.Lexical
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalGate
/-! A static owner/frame condition guards concrete five-way flow contracts.
The same physical location and native token are retained throughout lexical
children. Actual post-state reads supply allocation readiness; the condition
contains no execution law and is independent of any runtime witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.Lexical.Gated
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (LexicalResult)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open RecursiveNamedLoopContracts (ExecutesAt)
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records) (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}

def PreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_trace : ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def ReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

theorem preserves_of_unguarded {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : Lexical.PreservesAtFor protocol functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code) :
    PreservesAtFor protocol condition functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial _condition trace
  exact meaning valid environments heaps locals agrees typed reference read unmapped initial trace

theorem reflects_of_unguarded {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : Lexical.ReflectsAtFor protocol functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code) :
    ReflectsAtFor protocol condition functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial _condition evaluated
  exact meaning valid environments heaps locals agrees typed reference read unmapped initial evaluated

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.Lexical.Gated
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
/-! Three-way lexical control retains the existing flow and stopping lexical
receipt. Each producer consumes a concrete state and returns its actual reached
state at the producer's entry scope and canonical environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (FlowRep)
open TypedLexicalControl (Restored LexicalResult)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

def PreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_trace : RecursiveNamedLoopContracts.ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def PreservesAt (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  PreservesAtFor protocol condition (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) mode statements expected type code

def ReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def ReflectsAt (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ReflectsAtFor protocol condition (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) mode statements expected type code

def HeadPreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def HeadPreservesAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  HeadPreservesAtFor protocol condition (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code

def HeadReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def HeadReflectsAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  HeadReflectsAtFor protocol condition (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code

/-- Forget the transition while retaining the original lexical receipt. -/
theorem PreservesAtFor.forget (conditionSatisfied : ∀ location native, condition location native) {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : PreservesAtFor protocol condition functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code) :
    RecursiveNamedLexicalContracts.PreservesAtFor (entry := ProtectedStateTransition.entry protocol)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped installed trace
  obtain ⟨initial⟩ := installed
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial (conditionSatisfied _ _) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

/-- Lift a legacy guarded receipt using its proved concrete effects. -/
theorem legacy_PreservesAtFor {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.PreservesAtFor (entry := guarded)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code) :
    PreservesAtFor (ProtectedStateTransition.Lexical.legacyProtocol guarded) (fun _ _ => True)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial _condition trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

/-- Forget the transition while retaining the original lexical receipt. -/
theorem ReflectsAtFor.forget (conditionSatisfied : ∀ location native, condition location native) {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ReflectsAtFor protocol condition functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code) :
    RecursiveNamedLexicalContracts.ReflectsAtFor (entry := ProtectedStateTransition.entry protocol)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped installed evaluated
  obtain ⟨initial⟩ := installed
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial (conditionSatisfied _ _) evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

/-- Lift a legacy guarded receipt using its proved concrete effects. -/
theorem legacy_ReflectsAtFor {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.ReflectsAtFor (entry := guarded)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code) :
    ReflectsAtFor (ProtectedStateTransition.Lexical.legacyProtocol guarded) (fun _ _ => True)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial _condition evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial.down evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

/-- Forget the transition while retaining the original lexical receipt. -/
theorem HeadPreservesAtFor.forget (conditionSatisfied : ∀ location native, condition location native) {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : HeadPreservesAtFor protocol condition functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code) :
    RecursiveNamedLexicalContracts.HeadPreservesAtFor (entry := ProtectedStateTransition.entry protocol)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped installed trace
  obtain ⟨initial⟩ := installed
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial (conditionSatisfied _ _) trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- Lift a legacy guarded receipt using its proved concrete effects. -/
theorem legacy_HeadPreservesAtFor {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.HeadPreservesAtFor (entry := guarded)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code) :
    HeadPreservesAtFor (ProtectedStateTransition.Lexical.legacyProtocol guarded) (fun _ _ => True)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial _condition trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial.down trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

/-- Forget the transition while retaining the original lexical receipt. -/
theorem HeadReflectsAtFor.forget (conditionSatisfied : ∀ location native, condition location native) {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : HeadReflectsAtFor protocol condition functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code) :
    RecursiveNamedLexicalContracts.HeadReflectsAtFor (entry := ProtectedStateTransition.entry protocol)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped installed evaluated
  obtain ⟨initial⟩ := installed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial (conditionSatisfied _ _) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- Lift a legacy guarded receipt using its proved concrete effects. -/
theorem legacy_HeadReflectsAtFor {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded)
    {validity : SourceSemantics.Context → Prop} {size : Nat}
    {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.HeadReflectsAtFor (entry := guarded)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code) :
    HeadReflectsAtFor (ProtectedStateTransition.Lexical.legacyProtocol guarded) (fun _ _ => True)
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial _condition evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

theorem legacy_expression_preserves {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (expressions context) faults guarded) :
    ProtectedStateTransition.PreservesAt (ProtectedStateTransition.Lexical.legacyProtocol guarded)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (expressions context) faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

theorem legacy_expression_reflects {guarded : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport guarded) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (expressions context) faults guarded) :
    ProtectedStateTransition.ReflectsAt (ProtectedStateTransition.Lexical.legacyProtocol guarded)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (expressions context) faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (FlowRep)
open TypedLexicalControl (Restored LexicalResult)
open ProtectedStateTransition
universe u v

/-- State readiness is separate from static Source sites and the runtime
protocol. Faults retain only the distinct fault facet. -/
structure Readiness {Records : Type v} (protocol : Protocol.{u, v} Records) where
  Ready : SourceSemantics.Context → ∀ {index : Index}, protocol.State index → Prop
  FaultReady : ∀ {index : Index}, protocol.State index → Prop
  ValueFacts : SourceSemantics.Context → Dynamic.Heap → Dynamic.Value → TypeSystem.Ty → Prop
  ready_fault : ∀ {context index} {state : protocol.State index}, Ready context state → FaultReady state
  fault_after : ∀ {initial reached : Index} (first : protocol.State initial) (last : protocol.State reached),
    FaultReady first → AdministrativePreserved initial.mapping initial.store reached.mapping reached.store → FaultReady last

variable {Records : Type v} {protocol : Protocol.{u, v} Records}

def Readiness.trivial (protocol : Protocol.{u, v} Records) : Readiness protocol where
  Ready := fun _ {_} _ => True
  FaultReady := fun {_} _ => True
  ValueFacts := fun _ _ _ _ => True
  ready_fault := fun _ => True.intro
  fault_after := fun _ _ _ _ => True.intro

variable (readiness : Readiness protocol)

def PostReady (context : SourceSemantics.Context) (outcome : Dynamic.ControlOutcome)
    {index : Index} (reached : protocol.State index) : Prop :=
  match outcome with
  | .fault _ => readiness.FaultReady reached
  | .fallthrough _ | .returned _ | .breaking _ | .continuing _ => readiness.Ready context reached

/-- The witness is the actual post, with its original relation and an
outcome-specific readiness receipt. -/
def Reached (context : SourceSemantics.Context) (outcome : Dynamic.ControlOutcome)
    {initial : Index} (first : protocol.State initial) (final : Index) : Prop :=
  ∃ reached : protocol.State final, protocol.Relates first reached ∧ PostReady readiness context outcome reached

variable {readiness}

theorem Reached.forget {context : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    {initial final : Index} {first : protocol.State initial}
    (post : Reached readiness context outcome first final) : Transition protocol first final :=
  ⟨post.choose, post.choose_spec.1⟩

theorem Reached.of_trivial {context : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    {initial final : Index} {first : protocol.State initial}
    (post : Transition protocol first final) : Reached (Readiness.trivial protocol) context outcome first final := by
  obtain ⟨reached, related⟩ := post
  exact ⟨reached, related, by cases outcome <;> exact True.intro⟩

variable (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

def PreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : RecursiveNamedLoopContracts.ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def ReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def HeadPreservesAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : headFacts context id expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def HeadReflectsAtFor (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : headFacts context id expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩



/-- Transfers use actual Source allocations and the actual allocator post.
Binding restoration changes only the reached witness's lexical index. -/
structure AllocationTransfers (bindings : Bindings protocol) (source : TypedSource) where
  absent : ∀ {initial reached : Index} (first : protocol.State initial) (last : protocol.State reached)
    {context nextContext : SourceSemantics.Context} {binder : TypedBinder} {location : Dynamic.Location},
    readiness.Ready context first → BinderExtends source.owner context binder nextContext →
    Dynamic.Heap.Allocates initial.heap binder.scheme.body none location reached.heap →
    AdministrativePreserved initial.mapping initial.store reached.mapping reached.store → readiness.Ready nextContext last
  initialized : ∀ {initial reached : Index} (first : protocol.State initial) (last : protocol.State reached)
    {context nextContext : SourceSemantics.Context} {binder : TypedBinder} {location : Dynamic.Location} {value : Dynamic.Value},
    readiness.Ready context first → BinderExtends source.owner context binder nextContext →
    readiness.ValueFacts context initial.heap value binder.scheme.body →
    Dynamic.Heap.Allocates initial.heap binder.scheme.body (some value) location reached.heap →
    AdministrativePreserved initial.mapping initial.store reached.mapping reached.store → readiness.Ready nextContext last
  restore_ready : ∀ {index : Index} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {type : Ty} {value : Value},
    BinderExtends source.owner context binder nextContext →
    ∀ (state : protocol.State (index.prepend binder.id type value)),
      readiness.Ready nextContext state → readiness.Ready context (bindings.restore state)
  restore_fault : ∀ {index : Index} {binder : TypedBinder} {type : Ty} {value : Value},
    ∀ (state : protocol.State (index.prepend binder.id type value)),
      readiness.FaultReady state → readiness.FaultReady (bindings.restore state)

/-- Actual expression slots have separate static Source facts. A successful
child keeps readiness and genuine raw value facts at its same reached heap. -/
def ExpressionPost (context : SourceSemantics.Context) (type : TypeSystem.Ty)
    (outcome : Dynamic.ExpressionOutcome) {index : Index} (reached : protocol.State index) : Prop :=
  match outcome with
  | .fault _ => readiness.FaultReady reached
  | .value value => readiness.Ready context reached ∧ readiness.ValueFacts context index.heap value type

section Expressions
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (certificate : GenericExpressionMeaning.Certificate)

def ExpressionPreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → exprFacts context id node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ExpressionPost protocol readiness context node.type outcome reached

def ExpressionReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → exprFacts context id node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ExpressionPost protocol readiness context node.type outcome reached
end Expressions


/-- Only actual Source expression slots can project static expression facts. -/
inductive ExpressionSlot (source : TypedSource) (id : StatementId) : ExpressionId → Prop where
  | returning {node expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression)) : ExpressionSlot source id expression
  | expression {node expression semicolon} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression semicolon) : ExpressionSlot source id expression
  | initialized {node binder expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some expression)) : ExpressionSlot source id expression
  | condition {node expression thenBody elseBody} (found : source.lookupStatement? id = some node)
      (form : node.form = .ifThen expression thenBody elseBody) : ExpressionSlot source id expression

/-- Static projection authenticates actual Source slots. Tail facts are
requested only after a genuine successful Source fallthrough prefix. -/
structure StaticSites
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
    (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
    (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  head : ∀ {context mode id rest expected}, facts context mode (id :: rest) expected → headFacts context id expected
  expression : ∀ {context id expected expression node}, headFacts context id expected →
    ExpressionSlot source id expression → source.lookupExpression? expression = some node → exprFacts context expression node
  block : ∀ {context id expected node statements}, headFacts context id expected →
    source.lookupStatement? id = some node → node.form = .block statements → facts context false statements expected
  branch : ∀ {context id expected node expression thenBody elseBody} (boolean : Bool), headFacts context id expected →
    source.lookupStatement? id = some node → node.form = .ifThen expression thenBody elseBody →
    facts context false (if boolean then thenBody else elseBody.getD []) expected
  tail : ∀ {context nextContext mode id rest expected node environment next before after},
    facts context mode (id :: rest) expected → source.lookupStatement? id = some node →
    (mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false) →
    Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough next) after →
    facts nextContext mode rest expected

theorem StaticSites.trivial (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    StaticSites (fun _ _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True) program evidence source := by
  constructor <;> intros <;> exact True.intro

theorem PostReady.restore_control {context : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    {index : Index} {state : protocol.State index} (environment : Dynamic.Environment)
    (post : PostReady readiness context outcome state) :
    PostReady readiness context (Dynamic.restoreControl environment outcome) state := by
  cases outcome <;> exact post

theorem AllocationTransfers.restore_post {bindings : Bindings protocol} {source : TypedSource}
    (transfers : AllocationTransfers protocol readiness bindings source)
    {index : Index} {context nextContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    {binder : TypedBinder} {type : Ty} {value : Value}
    (extended : BinderExtends source.owner context binder nextContext)
    (state : protocol.State (index.prepend binder.id type value))
    (post : PostReady readiness nextContext outcome state) :
    PostReady readiness context outcome (bindings.restore state) := by
  cases outcome with
  | fault => exact transfers.restore_fault state post
  | fallthrough | returned | breaking | continuing => exact transfers.restore_ready extended state post

theorem AllocationTransfers.trivial (bindings : Bindings protocol) (source : TypedSource) :
    AllocationTransfers protocol (Readiness.trivial protocol) bindings source := by
  constructor <;> intros <;> exact True.intro

theorem PreservesAtFor.of_true {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (old : Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) mode statements expected type code) : PreservesAtFor protocol (Readiness.trivial protocol) condition (fun _ _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) mode statements expected type code := by
  intro valid _ mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditionProof _ trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := old valid environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, Reached.of_trivial post⟩

theorem PreservesAtFor.forget_true {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (strong : PreservesAtFor protocol (Readiness.trivial protocol) condition (fun _ _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) mode statements expected type code) : Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.PreservesAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := strong valid trivial environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post.forget⟩

theorem ReflectsAtFor.of_true {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (old : Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) mode statements expected type code) : ReflectsAtFor protocol (Readiness.trivial protocol) condition (fun _ _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) mode statements expected type code := by
  intro valid _ mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditionProof _ evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := old valid environments heaps locals agrees actualTyped reference read unmapped initial conditionProof evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, Reached.of_trivial post⟩

theorem ReflectsAtFor.forget_true {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (strong : ReflectsAtFor protocol (Readiness.trivial protocol) condition (fun _ _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) mode statements expected type code) : Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditionProof evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := strong valid trivial environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trivial evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post.forget⟩

theorem HeadPreservesAtFor.of_true {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (old : Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.HeadPreservesAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) id expected type code) : HeadPreservesAtFor protocol (Readiness.trivial protocol) condition (fun _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) id expected type code := by
  intro valid _ mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditionProof _ trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := old valid environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, Reached.of_trivial post⟩

theorem HeadPreservesAtFor.forget_true {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (strong : HeadPreservesAtFor protocol (Readiness.trivial protocol) condition (fun _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) id expected type code) : Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.HeadPreservesAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := strong valid trivial environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trivial trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

theorem HeadReflectsAtFor.of_true {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (old : Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.HeadReflectsAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) id expected type code) : HeadReflectsAtFor protocol (Readiness.trivial protocol) condition (fun _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) id expected type code := by
  intro valid _ mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditionProof _ evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := old valid environments heaps locals agrees actualTyped reference read unmapped initial conditionProof evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, Reached.of_trivial post⟩

theorem HeadReflectsAtFor.forget_true {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (strong : HeadReflectsAtFor protocol (Readiness.trivial protocol) condition (fun _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) id expected type code) : Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.HeadReflectsAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) functions program evidence size (scope := scope) id expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditionProof evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := strong valid trivial environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trivial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

section ExpressionCompatibility
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (certificate : GenericExpressionMeaning.Certificate)
theorem ExpressionPreservesAt.of_true {size : Nat} (old : ProtectedStateTransition.PreservesAt protocol model program context evidence source certificate faults size) : ExpressionPreservesAt protocol (Readiness.trivial protocol) program evidence model (fun _ _ _ => True) certificate (source := source) (context := context) (faults := faults) size := by
  intro scope id lowered certified node found _ mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial _ trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := old certified found environments heaps locals agrees actualTyped initial trace
  obtain ⟨reached, related⟩ := post
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, by cases outcome <;> simp [ExpressionPost, Readiness.trivial]⟩
end ExpressionCompatibility

section ExpressionCompatibility
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (certificate : GenericExpressionMeaning.Certificate)
theorem ExpressionReflectsAt.of_true {size : Nat} (old : ProtectedStateTransition.ReflectsAt protocol model program context evidence source certificate faults size) : ExpressionReflectsAt protocol (Readiness.trivial protocol) program evidence model (fun _ _ _ => True) certificate (source := source) (context := context) (faults := faults) size := by
  intro scope id lowered certified node found _ mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped initial _ evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := old certified found environments heaps locals agrees actualTyped initial evaluated
  obtain ⟨reached, related⟩ := post
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, by cases outcome <;> simp [ExpressionPost, Readiness.trivial]⟩
end ExpressionCompatibility

theorem Reached.continue {context : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    {initial middle final : Index} {first : protocol.State initial} {second : protocol.State middle}
    (related : protocol.Relates first second) (post : Reached readiness context outcome second final) :
    Reached readiness context outcome first final := by
  obtain ⟨reached, last, ready⟩ := post
  exact ⟨reached, protocol.trans related last, ready⟩

theorem Reached.restore_control {context : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    {initial final : Index} {first : protocol.State initial} (environment : Dynamic.Environment)
    (post : Reached readiness context outcome first final) :
    Reached readiness context (Dynamic.restoreControl environment outcome) first final := by
  obtain ⟨reached, related, ready⟩ := post
  exact ⟨reached, related, PostReady.restore_control (protocol := protocol) (readiness := readiness) environment ready⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts.Stateful.WithReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeControl
/-! Five-way heads keep the actual reached state along with restored source
control. Static conditions guard frame readiness without asserting body meaning.
Legacy observation contracts keep their original names and types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored)
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
def HeadPreservesAtWith (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def HeadPreservesAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  HeadPreservesAtWith (entry := entry) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code
    (values := values) (source := source) (context := context) (registry := registry) (administrative := administrative)
    (frameLayout := frameLayout) (globals := globals) (faults := faults)

def HeadReflectsAtWith (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_installed : entry scope mapping world before store canonical)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def HeadReflectsAt (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  HeadReflectsAtWith (entry := entry) functions program evidence
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) size (scope := scope) id expected type code
    (values := values) (source := source) (context := context) (registry := registry) (administrative := administrative)
    (frameLayout := frameLayout) (globals := globals) (faults := faults)


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored)
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep}

def HeadPreservesAtWith (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def HeadReflectsAtWith (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful

/-! Actual readiness belongs to the reached state. All five control outcomes
keep their original meaning; faults carry the separate fault facet. -/
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored)
open TypedLexicalControl (LexicalResult)
open RecursiveNamedLoopContracts (ExecutesAt)
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (readiness : Readiness protocol) (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}

def PreservesAtWith (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def ReflectsAtWith (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def HeadPreservesAtWith (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : headFacts context id expected)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def HeadReflectsAtWith (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : headFacts context id expected)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

theorem PreservesAtWith.of_true {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (old : Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) mode statements expected type code) : PreservesAtWith protocol (Readiness.trivial protocol) condition (fun _ _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) mode statements expected type code := by
  intro valid _ mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditionProof _ trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := old valid environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, Reached.of_trivial post⟩

theorem PreservesAtWith.forget_true {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (strong : PreservesAtWith protocol (Readiness.trivial protocol) condition (fun _ _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) mode statements expected type code) : Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := strong valid trivial environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post.forget⟩

theorem ReflectsAtWith.of_true {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (old : Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) mode statements expected type code) : ReflectsAtWith protocol (Readiness.trivial protocol) condition (fun _ _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) mode statements expected type code := by
  intro valid _ mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditionProof _ evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := old valid environments heaps locals agrees actualTyped reference read unmapped initial conditionProof evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, Reached.of_trivial post⟩

theorem ReflectsAtWith.forget_true {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (strong : ReflectsAtWith protocol (Readiness.trivial protocol) condition (fun _ _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) mode statements expected type code) : Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditionProof evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ := strong valid trivial environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trivial evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post.forget⟩

theorem HeadPreservesAtWith.of_true {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (old : Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful.HeadPreservesAtWith protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) id expected type code) : HeadPreservesAtWith protocol (Readiness.trivial protocol) condition (fun _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) id expected type code := by
  intro valid _ mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditionProof _ trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := old valid environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, Reached.of_trivial post⟩

theorem HeadPreservesAtWith.forget_true {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (strong : HeadPreservesAtWith protocol (Readiness.trivial protocol) condition (fun _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) id expected type code) : Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful.HeadPreservesAtWith protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := strong valid trivial environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trivial trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

theorem HeadReflectsAtWith.of_true {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (old : Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful.HeadReflectsAtWith protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) id expected type code) : HeadReflectsAtWith protocol (Readiness.trivial protocol) condition (fun _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) id expected type code := by
  intro valid _ mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditionProof _ evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := old valid environments heaps locals agrees actualTyped reference read unmapped initial conditionProof evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, Reached.of_trivial post⟩

theorem HeadReflectsAtWith.forget_true {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} (strong : HeadReflectsAtWith protocol (Readiness.trivial protocol) condition (fun _ _ _ => True) (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) id expected type code) : Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful.HeadReflectsAtWith protocol condition (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) functions program evidence size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditionProof evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post⟩ := strong valid trivial environments heaps locals agrees actualTyped reference read unmapped initial conditionProof trivial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Control.Stateful.WithReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateWhileReady
/-! Readiness travels beside the actual reached loop state. Static condition
and body receipts remain separate from the protocol and its records. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open ProtectedStateTransition
open RecursiveNamedLoopContracts (ExecutesAt)
open TypedLexicalControl (LexicalResult)
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)

/-- The activation facet is restricted to the real self-cell store and world.
It consumes the actual retained activation witness and its original effects. -/
structure ActivationTransfers (readiness : Readiness protocol) where
  ready : ∀ {context : SourceSemantics.Context} {scope : Scope} {mapping : LocationMap}
    {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {type : Ty} {condition body : Expr} {reason : Word},
    ∀ (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
      (reached : protocol.State ⟨scope, mapping, TypedLexicalWhile.installedWorld world type, heap,
        TypedLexicalWhile.installedStore store type condition body (LocalLoop.fallthrough type) reason actual, canonical⟩),
      AdministrativePreserved mapping store mapping
        (TypedLexicalWhile.installedStore store type condition body (LocalLoop.fallthrough type) reason actual) →
      protocol.Relates initial reached → protocol.records reached = protocol.records initial →
      readiness.Ready context initial → readiness.Ready context reached

theorem ActivationTransfers.trivial : ActivationTransfers protocol (Readiness.trivial protocol) where
  ready := fun _ _ _ _ _ _ => True.intro

/-- The constant readiness specialization keeps the exact original expression
post and adds only proof receipts. -/
theorem expression_preserves_trivial
    {source : TypedSource} {context : SourceSemantics.Context} {program : Program}
    {evidence : Dynamic.EvidenceEnvironment} {faults : FunctionCalls.FaultRep}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {certificate : GenericExpressionMeaning.Certificate} {size : Nat}
    (meaning : ProtectedStateTransition.PreservesAt protocol model program context evidence source certificate faults size) :
    ExpressionPreservesAt protocol (Readiness.trivial protocol) (context := context) (source := source)
      (faults := faults) program evidence model (fun _ _ _ => True) certificate size := by
  intro scope id lowered tree node found _facts mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial _ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ :=
    meaning tree found environments heaps locals agrees typed initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, by cases outcome <;> simp only [ExpressionPost, Readiness.trivial] <;> trivial⟩

theorem expression_reflects_trivial
    {source : TypedSource} {context : SourceSemantics.Context} {program : Program}
    {evidence : Dynamic.EvidenceEnvironment} {faults : FunctionCalls.FaultRep}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {certificate : GenericExpressionMeaning.Certificate} {size : Nat}
    (meaning : ProtectedStateTransition.ReflectsAt protocol model program context evidence source certificate faults size) :
    ExpressionReflectsAt protocol (Readiness.trivial protocol) (context := context) (source := source)
      (faults := faults) program evidence model (fun _ _ _ => True) certificate size := by
  intro scope id lowered tree node found _facts mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial _ready completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ :=
    meaning tree found environments heaps locals agrees typed initial completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, by cases outcome <;> simp only [ExpressionPost, Readiness.trivial] <;> trivial⟩

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}

variable {administrative : Core.Context}

/-- Constant facets preserve every field of the original actual body result. -/
theorem body_preserves_trivial (validity : SourceSemantics.Context → Prop)
    {scope : Scope} {size : Nat} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol (Readiness.trivial protocol) guard (fun _ _ _ _ => True) functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code := by
  intro valid _facts mapping world actualContext environment canonical actual before after store ξ contextLocation native
    outcome finalContext environments heaps locals agrees typed reference read unmapped initial guarded _ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, lexical, transition⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, lexical, Reached.of_trivial transition⟩

/-- Constant facets preserve every field of the original actual body result. -/
theorem body_reflects_trivial (validity : SourceSemantics.Context → Prop)
    {scope : Scope} {size : Nat} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol (Readiness.trivial protocol) guard (fun _ _ _ _ => True) functions program evidence validity
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code := by
  intro valid _facts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native
    value environments heaps locals agrees typed reference read unmapped initial guarded _ready completed
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, lexical, transition⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded completed
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, lexical, Reached.of_trivial transition⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateWhileEdges
/-! The existing measured condition and body edges relay their actual child
post-witness. Hidden native slots only affect the actual environment and
renaming. The original source grade and native completion are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

variable {certificate : GenericExpressionMeaning.Certificate} {body : Expr}

open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)

theorem condition_preserves_at {size : Nat}
    (meaning : ExpressionPreservesAt protocol readiness
      (context := context) (source := source) (faults := faults) program evidence
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (conditionFacts : exprFacts context condition node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : readiness.Ready context state.retained)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
        ExpressionPost protocol readiness context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    meaning tree found conditionFacts state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained, post⟩

theorem condition_reflects_at {size : Nat}
    (reflection : ExpressionReflectsAt protocol readiness
      (context := context) (source := source) (faults := faults) program evidence
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (conditionFacts : exprFacts context condition node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : readiness.Ready context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
        ExpressionPost protocol readiness context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    reflection tree found conditionFacts state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, post⟩

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem body_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard facts functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (bodyFacts : facts context false statements expected)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (ready : readiness.Ready context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
        PostReady readiness context outcome reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, lexical, last, retained, post⟩ :=
    correct valid bodyFacts state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, post, lexical⟩

theorem body_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness guard facts functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (bodyFacts : facts context false statements expected)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (ready : readiness.Ready context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
        PostReady readiness context outcome reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, lexical, last, retained, post⟩ :=
    correct valid bodyFacts state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    ⟨state.live.progress progress, last⟩
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post, lexical⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful.WithReady

namespace Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

variable {certificate : GenericExpressionMeaning.Certificate} {body : Expr}

theorem condition_preserves_at {size : Nat}
    (meaning : ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, progress, reached, retained, _post⟩ :=
    WithReady.condition_preserves_at (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) functions program evidence (WithReady.expression_preserves_trivial protocol meaning) tree found True.intro agrees state True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, progress, reached, retained⟩

theorem condition_reflects_at {size : Nat}
    (reflection : ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, _post⟩ :=
    WithReady.condition_reflects_at (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) functions program evidence (WithReady.expression_reflects_trivial protocol reflection) tree found True.intro agrees state True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained⟩

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem body_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, reached, retained, _post, lexical⟩ :=
    WithReady.body_preserves_at_for (protocol := protocol) (guard := guard) (validity := validity)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (facts := fun _ _ _ _ => True) functions program evidence (WithReady.body_preserves_trivial protocol guard functions program evidence validity correct) valid True.intro agrees reference state read guarded True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, reached, retained, lexical⟩

theorem body_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.While.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, retained, _post, lexical⟩ :=
    WithReady.body_reflects_at_for (protocol := protocol) (guard := guard) (validity := validity)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (facts := fun _ _ _ _ => True) functions program evidence (WithReady.body_reflects_trivial protocol guard functions program evidence validity correct) valid True.intro agrees reference state read guarded True.intro evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, retained, lexical⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedWhile.Body.Stateful
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateFor
/-! The real for activation, including its post code, and its protected state have separate
fields. Child transitions retain their reached state; installing the hidden
self cell is an administrative operation with an unchanged record observation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.For
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext installedStore installedWorld)
open TypedImperativeFor (LoopState Progress)
universe u v
variable {Records : Type v}

structure State (protocol : Protocol.{u, v} Records)
    (values : ValuesContext) {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (context : SourceSemantics.Context) (scope : Scope) (administrative actualContext : Core.Context)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (contextLocation location : Location) (type : Ty) (condition body post : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  live : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
    contextLocation location type condition body post reason mapping world heap store
  retained : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩

variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {contextLocation location : Location} {type : Ty} {condition body post : Expr} {reason : Word}
  {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {before after : Dynamic.Heap} {store futureStore : Store}
  {Records : Type v} {protocol : Protocol.{u, v} Records}

/-- Keep the actual child post-witness while transporting the live loop frame. -/
theorem State.reach
    (state : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body post reason mapping world before store)
    (progress : Progress values registry functions before after mapping futureMap world futureWorld store futureStore)
    (transition : Transition protocol state.retained
      ⟨scope, futureMap, futureWorld, after, futureStore, canonical⟩) :
    ∃ reached : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation location type condition body post reason futureMap futureWorld after futureStore,
      protocol.Relates state.retained reached.retained := by
  obtain ⟨final, related⟩ := transition
  exact ⟨⟨state.live.progress progress, final⟩, related⟩

/-- Install the real self cell, retaining the exact input records. -/
def install (transport : AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (typed : HasType actualContext (LocalLoop.iterate type condition body post reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type condition body post reason mapping
      (installedWorld world type) before
      (installedStore store type condition body post reason actual) := by
  have facts := TypedImperativeFor.install reason heaps actualTyped typed
  refine ⟨?_, transport.extend initial (.refl mapping) facts.2.1 facts.2.2.2.2.2
    (Dynamic.HeapMetadataExtend.refl before)⟩
  obtain ⟨finalHeaps, worlds, selfUnmapped, selfTyped, selfRead, preserved⟩ := facts
  obtain ⟨contextUnmapped, contextRead⟩ := TypedLexicalWhile.retain unmapped read preserved
  exact ⟨environments.extend (.refl mapping) worlds, finalHeaps, locals, actualTyped.weaken worlds,
    ⟨native, contextRead⟩, contextUnmapped, selfTyped, selfRead, selfUnmapped⟩


theorem install_related (transport : AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (typed : HasType actualContext (LocalLoop.iterate type condition body post reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    protocol.Relates initial (install transport environments heaps locals actualTyped typed read unmapped initial).retained := by
  dsimp only [install]
  apply transport.related

theorem install_records (transport : AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (typed : HasType actualContext (LocalLoop.iterate type condition body post reason)
      (LocalLoop.resultType type) ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    protocol.records (install transport environments heaps locals actualTyped typed read unmapped initial).retained = protocol.records initial := by
  dsimp only [install]
  apply transport.records_eq

/-- Source typing installs the actual renamed for closure and returns its
complete administrative progress, input relation, and exact record equality. -/
theorem initial_state (transport : AdministrativeTransport protocol)
    {conditionCode bodyCode postCode : Expr} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode bodyCode postCode reason) (LocalLoop.resultType type) ambient.definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩) :
    ∃ state : State protocol values registry functions context scope administrative actualContext frameLayout
      environment canonical actual contextLocation store.length type (conditionCode.rename ξ) (bodyCode.rename ξ)
      (postCode.rename ξ) reason mapping (installedWorld world type) before
      (installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (postCode.rename ξ) reason actual),
      Progress values registry functions before before mapping mapping world (installedWorld world type) store
        (installedStore store type (conditionCode.rename ξ) (bodyCode.rename ξ) (postCode.rename ξ) reason actual) ∧
      protocol.Relates initial state.retained ∧ protocol.records state.retained = protocol.records initial := by
  have actualCode := typed.rename
    (TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees)
  rw [LoopRenaming.iterate] at actualCode
  let state := install transport environments heaps locals actualTyped actualCode read unmapped initial
  have facts := TypedImperativeFor.install reason heaps actualTyped actualCode
  exact ⟨state, ⟨state.live.heaps, .refl _, facts.2.1, facts.2.2.2.2.2, .refl _⟩,
    install_related transport environments heaps locals actualTyped actualCode read unmapped initial,
    install_records transport environments heaps locals actualTyped actualCode read unmapped initial⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.For
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateForContracts
/-! Measured post-header edges consume the actual body state. Their real
six-slot native prefix, source trace, and independent native grade remain the
existing for contract. Successful and fault edges return the actual state at
the fixed loop scope after removing any post-header binders. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Progress postValues)
open ProtectedStateTransition
universe u v
variable {Records : Type v}

def PostPreservesAt (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment},
    ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
    guard contextLocation native →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after →
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained

def PostFaultsAt (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
    ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
    guard contextLocation native →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained

def PostReflectsAt (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
    ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
    guard contextLocation native →
    ∀ continued : Bool,
    EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ)) value finalStore →
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained)

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateForReady
/-! Measured post-header edges consume the actual body state. Their real
six-slot native prefix, source trace, and independent native grade remain the
existing for contract. Successful and fault edges return the actual state at
the fixed loop scope after removing any post-header binders. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Progress postValues)
open ProtectedStateTransition
universe u v
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable {Records : Type v}

/-- Readiness of the actual retained self-cell activation follows only its
real installed store/world and original administrative receipts. -/
structure ActivationTransfers (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) where
  ready : ∀ {context : SourceSemantics.Context} {scope : Scope} {mapping : LocationMap}
    {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {type : Ty} {condition body post : Expr} {reason : Word},
    ∀ (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
      (reached : protocol.State ⟨scope, mapping, TypedLexicalWhile.installedWorld world type, heap,
        TypedLexicalWhile.installedStore store type condition body post reason actual, canonical⟩),
      AdministrativePreserved mapping store mapping
        (TypedLexicalWhile.installedStore store type condition body post reason actual) →
      protocol.Relates initial reached → protocol.records reached = protocol.records initial →
      readiness.Ready context initial → readiness.Ready context reached

theorem ActivationTransfers.trivial (protocol : Protocol.{u, v} Records) :
    ActivationTransfers protocol (Readiness.trivial protocol) where
  ready := fun _ _ _ _ _ _ => True.intro

def PostPreservesAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment},
    ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
    guard contextLocation native →
    readiness.Ready context state.retained →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after →
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained

def PostFaultsAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
    ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
    guard contextLocation native →
    readiness.Ready context state.retained →
    ∀ continued : Bool,
    SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.FaultReady reached.retained

def PostReflectsAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
    ∀ state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store,
    ∀ {native : CallableIndexedHistory.NativeFrame},
    store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native) →
    guard contextLocation native →
    readiness.Ready context state.retained →
    ∀ continued : Bool,
    EvaluationSize size (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ)) value finalStore →
    (∃ sourceSize finalContext finalEnvironment after finalMap finalWorld,
      SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained) ∨
    (∃ sourceSize finalContext reason token after finalMap finalWorld,
      SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.FaultReady reached.retained)


theorem post_preserves_trivial (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr)
    (meaning : ProtectedFor.Body.Stateful.PostPreservesAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) items code) :
    PostPreservesAt protocol (Readiness.trivial protocol) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) items code := by
  intro mapping world before after store finalContext finalEnvironment state native read guarded _ready continued trace
  obtain ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related⟩ := meaning state read guarded continued trace
  exact ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related, True.intro⟩

theorem post_faults_trivial (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr)
    (meaning : ProtectedFor.Body.Stateful.PostFaultsAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) (faults := faults) items code) :
    PostFaultsAt protocol (Readiness.trivial protocol) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) (faults := faults) items code := by
  intro mapping world before after store finalContext reason state native read guarded _ready continued trace
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, progress, reached, related⟩ := meaning state read guarded continued trace
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, progress, reached, related, True.intro⟩

theorem post_reflects_trivial (protocol : Protocol.{u, v} Records) (guard : Location → CallableIndexedHistory.NativeFrame → Prop) (size : Nat) {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr)
    (meaning : ProtectedFor.Body.Stateful.PostReflectsAt protocol guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) faults items code) :
    PostReflectsAt protocol (Readiness.trivial protocol) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode) (body := body) (selfReason := selfReason) faults items code := by
  intro mapping world before store finalStore value state native read guarded _ready continued completed
  rcases meaning state read guarded continued completed with good | bad
  · obtain ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, trace, same, progress, reached, related⟩ := good
    exact Or.inl ⟨sourceSize, finalContext, finalEnvironment, after, finalMap, finalWorld, trace, same, progress, reached, related, True.intro⟩
  · obtain ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, progress, reached, related⟩ := bad
    exact Or.inr ⟨sourceSize, finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, progress, reached, related, True.intro⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateForEdges
/-! The existing measured condition and body edges relay their actual child
post-witness. Hidden native slots only affect the actual environment and
renaming. The original source grade and native completion are retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open TypedImperativeFor (Progress)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

variable {certificate : GenericExpressionMeaning.Certificate} {body : Expr}

open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)

/-- Generic child meaning is an internal composition interface. The concrete
named consumer supplies it from the accepted recursive expression Tree. -/
theorem condition_preserves_at {size : Nat}
    (meaning : ExpressionPreservesAt protocol readiness (context := context) (source := source) (faults := faults)
      program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (conditionFacts : exprFacts context condition node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    (ready : readiness.Ready context state.retained)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ ExpressionPost protocol readiness context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    meaning tree found conditionFacts state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached := (⟨state.live.progress progress, last⟩ : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore)
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained, post⟩

/-- Actual completed condition code recovers the independent source outcome
and transports the original guard through the observed prefix effects. -/
theorem condition_reflects_at {size : Nat}
    (reflection : ExpressionReflectsAt protocol readiness (context := context) (source := source) (faults := faults)
      program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts certificate size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (conditionFacts : exprFacts context condition node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    (ready : readiness.Ready context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ ExpressionPost protocol readiness context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, last, retained, post⟩ :=
    reflection tree found conditionFacts state.live.environments state.live.heaps state.live.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)) state.retained ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached := (⟨state.live.progress progress, last⟩ : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, post⟩


variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

/-- The body contract is an internal composition interface. Recursive statement
induction supplies it for the current child, including control transfers. -/
theorem body_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard facts functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (bodyFacts : facts context false statements expected)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (ready : readiness.Ready context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ PostReady readiness context outcome reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, lexical, last, retained, post⟩ :=
    correct valid bodyFacts state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready trace
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached := (⟨state.live.progress progress, last⟩ : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore)
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, post, lexical⟩


/-- A completed body reconstructs its independent source trace and reached
lexical context while retaining the original outer installed entry. -/
theorem body_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness guard facts functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (bodyFacts : facts context false statements expected)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (ready : readiness.Ready context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ PostReady readiness context outcome reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, lexical, last, retained, post⟩ :=
    correct valid bodyFacts state.live.environments state.live.heaps state.live.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.live.selfTyped) state.live.actualTyped)))
      reference read state.live.contextUnmapped state.retained guarded ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress values registry functions before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata⟩
  let reached := (⟨state.live.progress progress, last⟩ : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore)
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post, lexical⟩


end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful.WithReady

namespace Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext FlowRep)
open TypedImperativeFor (Progress)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope} {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

variable {certificate : GenericExpressionMeaning.Certificate} {body : Expr}

theorem condition_preserves_at {size : Nat}
    (meaning : ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, progress, reached, retained, _post⟩ :=
    WithReady.condition_preserves_at (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) functions program evidence
      (ProtectedWhile.Body.Stateful.WithReady.expression_preserves_trivial protocol meaning) tree found True.intro agrees state True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, progress, reached, retained⟩

theorem condition_reflects_at {size : Nat}
    (reflection : ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, _post⟩ :=
    WithReady.condition_reflects_at (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
      (exprFacts := fun _ _ _ => True) functions program evidence
      (ProtectedWhile.Body.Stateful.WithReady.expression_reflects_trivial protocol reflection) tree found True.intro agrees state True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained⟩

variable (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

theorem body_preserves_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, reached, retained, _post, lexical⟩ :=
    WithReady.body_preserves_at_for (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) (guard := guard) (facts := fun _ _ _ _ => True)
      functions program evidence validity
      (ProtectedWhile.Body.Stateful.WithReady.body_preserves_trivial protocol guard functions program evidence validity correct)
      valid True.intro agrees reference state read guarded True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress, reached, retained, lexical⟩

theorem body_reflects_at_for (validity : SourceSemantics.Context → Prop) {size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence validity
      (administrative := administrative) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frameLayout)
      (globals := globals) (scope := scope) size false statements expected type code)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after := by
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, retained, _post, lexical⟩ :=
    WithReady.body_reflects_at_for (protocol := protocol) (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) (guard := guard) (facts := fun _ _ _ _ => True)
      functions program evidence validity
      (ProtectedWhile.Body.Stateful.WithReady.body_reflects_trivial protocol guard functions program evidence validity correct)
      valid True.intro agrees reference state read guarded True.intro evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, progress, reached, retained, lexical⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedFor.Body.Stateful
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchReady
/-! Match readiness is established at the actual combined prefix post. The
pure Source hidden and pattern allocations justify its heap; no intermediate
protocol witness is assumed. Restoration consumes the actual later body post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (readiness : Readiness protocol) (source : TypedSource)

structure PrefixTransfers where
  hidden : ∀ {initial reached : Index} (first : protocol.State initial) (last : protocol.State reached)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {value : Dynamic.Value} {location : Dynamic.Location},
    readiness.Ready context first → readiness.ValueFacts context initial.heap value type →
    Dynamic.Heap.Allocates initial.heap type (some value) location reached.heap →
    AdministrativePreserved initial.mapping initial.store reached.mapping reached.store → readiness.Ready context last
  arm : ∀ {initial reached : Index} (first : protocol.State initial) (last : protocol.State reached)
    {context armContext : SourceSemantics.Context} {control : ControlContext} {resolution : MatchResolution}
    {type : TypeSystem.Ty} {caseFacts : List BodyFacts} {value : Dynamic.Value} {hidden : Dynamic.Heap}
    {location : Dynamic.Location} {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    {environment armEnvironment : Dynamic.Environment},
    readiness.Ready context first → readiness.ValueFacts context initial.heap value type →
    Dynamic.Heap.Allocates initial.heap type (some value) location hidden →
    MatchCasesHaveType source control context type resolution.cases caseFacts →
    Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings) →
    BindersExtend source.owner context (bindings.map Prod.fst) armContext →
    Dynamic.BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment reached.heap →
    AdministrativePreserved initial.mapping initial.store reached.mapping reached.store → readiness.Ready armContext last
  restore_arm : ∀ {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ReturnTo protocol scope canonical selectedScope selectedCanonical)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder},
    BindersExtend source.owner context binders armContext →
    ∀ {mapping world heap store} (state : protocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩),
      readiness.Ready armContext state → readiness.Ready context (returnTo.restore state)
  restore_parent : ∀ {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ReturnTo protocol scope canonical selectedScope selectedCanonical)
    {context : SourceSemantics.Context},
    ∀ {mapping world heap store} (state : protocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩),
      readiness.Ready context state → readiness.Ready context (returnTo.restore state)

variable {protocol readiness source}

theorem PrefixTransfers.trivial (protocol : Protocol.{u, v} Records) (source : TypedSource) :
    PrefixTransfers protocol (Readiness.trivial protocol) source where
  hidden := by intros; exact True.intro
  arm := by intros; exact True.intro
  restore_arm := by intros; exact True.intro
  restore_parent := by intros; exact True.intro

theorem PrefixTransfers.post_arm (transfers : PrefixTransfers protocol readiness source)
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ReturnTo protocol scope canonical selectedScope selectedCanonical)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder}
    (extended : BindersExtend source.owner context binders armContext)
    {mapping world heap store} (state : protocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (environment : Dynamic.Environment)
    {outcome : Dynamic.ControlOutcome} (post : PostReady readiness armContext outcome state) :
    PostReady readiness context (Dynamic.restoreControl environment outcome) (returnTo.restore state) := by
  cases outcome with
  | fault => exact readiness.fault_after state (returnTo.restore state) post (AdministrativePreserved.refl _ _)
  | fallthrough | returned | breaking | continuing => exact transfers.restore_arm returnTo extended state post

theorem PrefixTransfers.post_parent (transfers : PrefixTransfers protocol readiness source)
    {scope selectedScope : SourceCoreLocalCell.Scope} {canonical selectedCanonical : Environment}
    (returnTo : ReturnTo protocol scope canonical selectedScope selectedCanonical)
    {context : SourceSemantics.Context}
    {mapping world heap store} (state : protocol.State ⟨selectedScope, mapping, world, heap, store, selectedCanonical⟩)
    (environment : Dynamic.Environment)
    {outcome : Dynamic.ControlOutcome} (post : PostReady readiness context outcome state) :
    PostReady readiness context (Dynamic.restoreControl environment outcome) (returnTo.restore state) := by
  cases outcome with
  | fault => exact readiness.fault_after state (returnTo.restore state) post (AdministrativePreserved.refl _ _)
  | fallthrough | returned | breaking | continuing => exact transfers.restore_parent returnTo state post

end Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchBodyContracts
/-! The bounded match child interfaces keep the actual selected-arm state and
fixed frame gate. Source selection and typing stay independent static receipts;
these callbacks are discharged by the surrounding body induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates
open CompatibleMatchSelectionPrefix DataMatchBranchPrefix
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {source : TypedSource}
  (program : Program) (parent : SourceSemantics.Context) (control : ControlContext)
  (evidence : Dynamic.EvidenceEnvironment) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty)
  {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : FunctionCalls.FaultRep} (budget : Nat)

def ArmPreservesBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := armContext) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def ArmPreservesBelow (outerScope : Scope) : Prop :=
  ArmPreservesBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)

def ArmReflectsBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := armContext) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def ArmReflectsBelow (outerScope : Scope) : Prop :=
  ArmReflectsBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)

def DefaultPreservesBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol guard functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := parent) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def DefaultPreservesBelow (outerScope : Scope) : Prop :=
  DefaultPreservesBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)

def DefaultReflectsBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    ∀ child, child < budget → ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol guard functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := parent) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def DefaultReflectsBelow (outerScope : Scope) : Prop :=
  DefaultReflectsBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) outerScope
    (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)


/-- The match head uses the same actual five-way head interface as control. -/
abbrev Head.HeadPreservesAtFor := @RecursiveNamedImperativeFor.Control.Stateful.HeadPreservesAtWith
abbrev Head.HeadReflectsAtFor := @RecursiveNamedImperativeFor.Control.Stateful.HeadReflectsAtWith


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds.Stateful

namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchBodyContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open ProtectedStateTransition

/-- The old entry receipt has both concrete binder operations. -/
def legacyBindings {guarded : ProtectedExpressionMeaning.Entry}
    (bindings : ProtectedExpressionMeaning.Binds guarded) : Bindings (Lexical.legacyProtocol guarded) where
  prepend state _ _ _ := ⟨bindings.prepend state.down⟩
  prepend_related _ _ _ _ := trivial
  prepend_records _ _ _ _ := rfl
  restore state := ⟨bindings.restore state.down⟩
  restore_related _ := trivial
  restore_records _ := rfl

section ExpressionAdapters
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {size : Nat} {guarded : ProtectedExpressionMeaning.Entry}

/-- The compatibility post observes the effects proved by the child. -/
theorem legacy_expression_preserves (transport : ProtectedExpressionMeaning.Transport guarded)
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults guarded) :
    ProtectedStateTransition.PreservesAt (Lexical.legacyProtocol guarded) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩

/-- Reflection keeps its independent Source grade and actual effects. -/
theorem legacy_expression_reflects (transport : ProtectedExpressionMeaning.Transport guarded)
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults guarded) :
    ProtectedStateTransition.ReflectsAt (Lexical.legacyProtocol guarded) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed initial.down evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨⟨transport.extend initial.down maps worlds frame metadata⟩, trivial⟩⟩
end ExpressionAdapters

end Solcore.SourceSemantics.CoreLowering.ProtectedStateMatchBodyContracts

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates
open CompatibleMatchSelectionPrefix DataMatchBranchPrefix
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)

variable {compilation : SourceCoreCompatibleDataMatches.Context}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {source : TypedSource}
  (program : Program) (parent : SourceSemantics.Context) (control : ControlContext)
  (evidence : Dynamic.EvidenceEnvironment) (resolution : MatchResolution)
  (bodyCertificate : BodyCertificate) (expected : TypeSystem.Ty) (type : Ty)
  {solved : List SolvedRequirement} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {faults : FunctionCalls.FaultRep} (budget : Nat)

def ArmPreservesBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    ∀ child, child < budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard (fun _ _ _ _ => True) functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := armContext) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def ArmReflectsBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.arm statements bindings) →
    SelectedBody bodyCertificate scope environment heap type (.arm statements bindings)
      finalScope finalEnvironment finalHeap body →
    ∀ {armContext staticFinal facts},
    BindersExtend source.owner parent (bindings.map Prod.fst) armContext →
    StatementsHaveType source control armContext statements staticFinal facts →
    ∀ child, child < budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness guard (fun _ _ _ _ => True) functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := armContext) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def DefaultPreservesBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    ∀ child, child < budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness guard (fun _ _ _ _ => True) functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := parent) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

def DefaultReflectsBelowFor (validity : SourceSemantics.Context → Prop) (outerScope : Scope) : Prop :=
  ∀ {sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body},
    scope.map Prod.fst = resolution.hiddenScrutinee :: outerScope.map Prod.fst →
    Dynamic.MatchCasesSelect parent sourceValue resolution.cases resolution.defaultBody (.default statements) →
    SelectedBody bodyCertificate scope environment heap type (.default statements)
      finalScope finalEnvironment finalHeap body →
    ∀ {staticFinal facts}, StatementsHaveType source control parent statements staticFinal facts →
    ∀ child, child < budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness guard (fun _ _ _ _ => True) functions program evidence (validity := validity) (values := compilation.values)
      (source := source) (context := parent) (registry := registry)
      (administrative := administrative) (frameLayout := frame) (globals := globals)
      (faults := faults) (scope := finalScope) child false statements expected type body

variable {validity : SourceSemantics.Context → Prop} {outerScope : Scope}

theorem ArmPreservesBelowFor.of_true
    (old : RecursiveNamedMatchSourceBounds.Stateful.ArmPreservesBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget validity outerScope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) :
    ArmPreservesBelowFor protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) guard functions program parent control evidence resolution bodyCertificate expected type budget validity outerScope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body scopeEq selected selectedBody armContext staticFinal facts extended typed child smaller
  exact RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith.of_true
    protocol guard functions program evidence (old scopeEq selected selectedBody extended typed child smaller)

theorem ArmReflectsBelowFor.of_true
    (old : RecursiveNamedMatchSourceBounds.Stateful.ArmReflectsBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget validity outerScope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) :
    ArmReflectsBelowFor protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) guard functions program parent control evidence resolution bodyCertificate expected type budget validity outerScope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements bindings finalScope finalEnvironment finalHeap body scopeEq selected selectedBody armContext staticFinal facts extended typed child smaller
  exact RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith.of_true
    protocol guard functions program evidence (old scopeEq selected selectedBody extended typed child smaller)

theorem DefaultPreservesBelowFor.of_true
    (old : RecursiveNamedMatchSourceBounds.Stateful.DefaultPreservesBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget validity outerScope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) :
    DefaultPreservesBelowFor protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) guard functions program parent control evidence resolution bodyCertificate expected type budget validity outerScope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body scopeEq selected selectedBody staticFinal facts typed child smaller
  exact RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith.of_true
    protocol guard functions program evidence (old scopeEq selected selectedBody typed child smaller)

theorem DefaultReflectsBelowFor.of_true
    (old : RecursiveNamedMatchSourceBounds.Stateful.DefaultReflectsBelowFor protocol guard functions program parent control evidence resolution bodyCertificate expected type budget validity outerScope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults)) :
    DefaultReflectsBelowFor protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) guard functions program parent control evidence resolution bodyCertificate expected type budget validity outerScope
      (source := source) (administrative := administrative) (frame := frame) (globals := globals) (registry := registry) (faults := faults) := by
  intro sourceValue scope environment heap statements finalScope finalEnvironment finalHeap body scopeEq selected selectedBody staticFinal facts typed child smaller
  exact RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith.of_true
    protocol guard functions program evidence (old scopeEq selected selectedBody typed child smaller)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedMatchSourceBounds.Stateful.WithReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateFunctionFinishReady
/-! The function finish retains the same reached flow state. Ordinary results
keep its success readiness. Source faults and escaped loop control keep its
fault facet; no heap or record witness is reconstructed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.FunctionFinish
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLexicalContracts.Stateful.WithReady (Readiness)
universe u v
variable {Records : Type v} {protocol : Protocol.{u, v} Records}
  (readiness : Readiness protocol)

def PostReady (context : SourceSemantics.Context) (outcome : Dynamic.ExpressionOutcome)
    {index : Index} (reached : protocol.State index) : Prop :=
  match outcome with
  | .value _ => readiness.Ready context reached
  | .fault _ => readiness.FaultReady reached

def Reached (context : SourceSemantics.Context) (outcome : Dynamic.ExpressionOutcome)
    {initial : Index} (first : protocol.State initial) (final : Index) : Prop :=
  ∃ reached : protocol.State final, protocol.Relates first reached ∧ PostReady readiness context outcome reached

variable {readiness}

theorem post_of_exit {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    {control : Dynamic.ControlOutcome} {outcome : Dynamic.ExpressionOutcome}
    {index : Index} {reached : protocol.State index}
    (exit : CompatibleNamedBody.Exit expected control outcome)
    (post : RecursiveNamedLexicalContracts.Stateful.WithReady.PostReady readiness context control reached) :
    PostReady readiness context outcome reached := by
  cases exit with
  | returned _ => exact post
  | unit _ _ => exact post
  | fault _ => exact post
  | breaking _ => exact readiness.ready_fault post
  | continuing _ => exact readiness.ready_fault post

theorem Reached.forget {context : SourceSemantics.Context} {outcome : Dynamic.ExpressionOutcome}
    {initial final : Index} {first : protocol.State initial}
    (post : Reached readiness context outcome first final) : Transition protocol first final := by
  obtain ⟨reached, related, _⟩ := post
  exact ⟨reached, related⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.FunctionFinish
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalSourceSites
/-! Genuine lexical Source syntax supplies facts at actual expression and
statement sites. Tail facts use the actual successful Source prefix, so a
stopping block or branch does not require typing its unexecuted suffix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalSourceSites
open Frontend SourceInference GenericLexicalStatements
open RecursiveNamedLexicalContracts.Stateful.WithReady

variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}

def HeadFacts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (id : StatementId) (expected : TypeSystem.Ty) : Prop :=
  ∃ mode rest, Syntax source expressionSyntax context mode (id :: rest) expected

def ExpressionFacts (source : TypedSource) (context : SourceSemantics.Context)
    (id : ExpressionId) (node : ExpressionNode) : Prop :=
  ExpressionHasType source context id node.type

theorem expression {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {child : ExpressionId} {node : ExpressionNode}
    (facts : HeadFacts source expressionSyntax context id expected)
    (slot : ExpressionSlot source id child)
    (found : source.lookupExpression? child = some node) :
    ExpressionFacts source context child node := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax <;> cases slot <;> simp_all [ExpressionFacts]

theorem block {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {statements : List StatementId}
    (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements) :
    Syntax source expressionSyntax context false statements expected := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax <;> simp_all

theorem branch {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (boolean : Bool) (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Syntax source expressionSyntax context false (if boolean then thenBody else elseBody.getD []) expected := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax <;> cases boolean <;> simp_all

theorem tail {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {context nextContext : SourceSemantics.Context} {mode : Bool} {id : StatementId}
    {rest : List StatementId} {expected : TypeSystem.Ty} {node : StatementNode}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (unique : NodeOccurrencesUnique source)
    (typedSyntax : Syntax source expressionSyntax context mode (id :: rest) expected)
    (found : source.lookupStatement? id = some node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (executed : Dynamic.StatementExecutes program context evidence source environment before id
      nextContext (.fallthrough next) after) :
    Syntax source expressionSyntax nextContext mode rest expected := by
  cases typedSyntax with
  | returnUnit _ found form sourceType =>
    obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique (lookupStatement?_sound found) form executed
    cases impossible
  | returnValue _ found form sourceType expressionFound valueType typed value =>
    obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique (lookupStatement?_sound found) form executed
    cases impossible
  | tail found form sourceType expressionFound valueType typed value =>
    have same := Option.some.inj (found.symm.trans ‹source.lookupStatement? id = some node›)
    subst same
    exact False.elim (notTail rfl rfl _ form)
  | uninitialized found form declaration monomorphic extended ordinary remaining =>
    obtain ⟨actualExtension, _⟩ := ScalarStatementViews.letUninitialized unique (lookupStatement?_sound found) form executed
    have same := Dynamic.BinderExtends.functional extended actualExtension
    exact same ▸ remaining
  | initialized found form declaration monomorphic extended ordinary initializerFound sourceType initializerTyped initializerSyntax remaining =>
    obtain ⟨actualExtension, _⟩ := ScalarStatementViews.letInitialized unique (lookupStatement?_sound found) form monomorphic executed
    have same := Dynamic.BinderExtends.functional extended actualExtension
    exact same ▸ remaining
  | discard found form notTail sourceType expressionFound typed value remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.expression unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | block found form sourceType inner remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | ifThen found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.ifThen unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | terminalBlock unique found form sourceType inner stops =>
    have impossible := block_terminates unique found form stops executed
    cases impossible
  | terminalIf unique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops =>
    have impossible := conditional_terminates unique found form thenStops elseStops executed
    cases impossible

theorem sites (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (unique : NodeOccurrencesUnique source) :
    StaticSites (Syntax source expressionSyntax) (HeadFacts source expressionSyntax)
      (ExpressionFacts source) program evidence source where
  head := fun typedSyntax => ⟨_, _, typedSyntax⟩
  expression := expression
  block := block
  branch := branch
  tail := tail unique

end Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalSourceSites
end
