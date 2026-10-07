import Solcore.SourceSemantics.CoreLowering.ProtectedState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts

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
