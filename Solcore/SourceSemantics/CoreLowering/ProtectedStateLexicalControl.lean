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
