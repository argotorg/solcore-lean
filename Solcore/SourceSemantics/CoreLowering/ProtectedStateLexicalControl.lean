import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexical
import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition

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
