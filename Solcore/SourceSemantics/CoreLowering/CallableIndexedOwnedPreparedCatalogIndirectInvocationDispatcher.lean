import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectLambdaInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds

/-! The actual admitted payload selects a closure, named global or builtin
application. This finite packet contains only retained compiler/runtime fields
and genuine Source argument typing. The dispatcher constructs each application
from its original leaf and strict body children. No packet stores an evaluation
or a completed body law. The enclosing ordered argument fold constructs this
packet at its actual reached state, and retains separate stage/arity outcomes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt NamedCapture)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (Association)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open RecursiveNamedCatalogInvocationBounds (Below)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {arguments : List Dynamic.Value} {payloads : List Value}

/-- A positive finite application packet is built at the actual argument post.
The Source typing fields are ordinary raw admission proofs, and the named
profile retains its genuine coupled compiler extraction. Neither direction of semantics is a field. -/
inductive Receipt : Dynamic.Value → Dynamic.EvidenceEnvironment → Value → TypeSystem.Ty → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
      (member : Association qualification headers keys bodyRegistry faults
        mapping world function native bindings parameterCore resultCore)
      (represented : CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world bindings arguments payloads)
      (beforeTyped : Dynamic.HeapWellTyped function.context before)
      (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
        (function.parameters.map (fun binder => binder.scheme.body)))
      (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured) :
      Receipt (.closure function) function.evidence native function.resultType resultCore
  | named {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
      (owner : OwnedKey keys) (member : header ∈ headers)
      (captureZero : owner.key.capturePrefix = 0)
      (globals : header.globals = compiled.indexed.base.globals.length)
      (sourceAt : NamedSourceAt header rawD source)
      (capture : NamedCapture headers owner.key header mapping world)
      (identity descriptor : Word)
      (represented : CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        mapping world header.bindings arguments payloads)
      (beforeTyped : Dynamic.HeapWellTyped header.function.context before)
      (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
      (sameLayouts : header.layouts = compiled.indexed.layouts)
      (profiles : CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
        (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
        functions owner (header := header))
      (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
        header.context (.statements true header.function.body) header.function.resultType) :
      Receipt (.global source) source.evidence
        (CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.carrier owner capture identity descriptor)
        header.function.resultType header.output
  | builtin {function : BuiltinFunctionId} {native : Value} {nativeType : Ty}
      (builtin : CallableIndexedBuiltinValues.Represents compiled.indexed world
        function.type (.builtin ⟨function⟩) native nativeType)
      (represented : ValuesRep compiled.compatible.checked registry functions mapping world
        function.parameterTypes arguments payloads (CompatibleBuiltinMeaning.argumentTypes function))
      (invocation : Dynamic.EvidenceEnvironment) :
      Receipt (.builtin ⟨function⟩) invocation native function.returnType (SourceCoreInteger.builtinResult function)

/-- The exact closure body is a strict F child of this application. -/
def ClosurePreservesBelow (budget : Nat) : Prop :=
  ∀ {mapping world function native bindings parameterCore resultCore},
    (member : Association qualification headers keys bodyRegistry faults
      mapping world function native bindings parameterCore resultCore) →
    Below budget (CallableIndexedOwnedPreparedDirectLambdaInvocationBounds.FlowPreserves
      functions member (registry := registry))

def ClosureReflectsBelow (budget : Nat) : Prop :=
  ∀ {mapping world function native bindings parameterCore resultCore},
    (member : Association qualification headers keys bodyRegistry faults
      mapping world function native bindings parameterCore resultCore) →
    Below budget (CallableIndexedOwnedPreparedDirectLambdaInvocationBounds.FlowReflects
      functions member (registry := registry))

/-- The global alternative consumes the same strict extracted Header/profile F child. -/
def NamedPreservesBelow (budget : Nat) : Prop :=
  ∀ (owner : OwnedKey keys)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)), header ∈ headers →
    Below budget (fun child => ∀ administrative
      (profile : CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.Profile
        (certificates := certificates) (expressionSyntax := expressionSyntax) header administrative),
      CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.FlowPreserves
        (registry := registry) (faults := faults) (headers := headers) functions owner profile child)

def NamedReflectsBelow (budget : Nat) : Prop :=
  ∀ (owner : OwnedKey keys)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)), header ∈ headers →
    Below budget (fun child => ∀ administrative
      (profile : CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.Profile
        (certificates := certificates) (expressionSyntax := expressionSyntax) header administrative),
      CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.FlowReflects
        (registry := registry) (faults := faults) (headers := headers) functions owner profile child)

section Caller
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world before store)
  (stable : StableRows (bridge.pool initial))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {function : Dynamic.Value} {invocation : Dynamic.EvidenceEnvironment} {native : Value}
  {sourceResult : TypeSystem.Ty} {resultCore : Ty}
  (receipt : Receipt (qualification := qualification) (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (before := before) (arguments := arguments) (payloads := payloads)
    functions function invocation native sourceResult resultCore)
  {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}

/-- Every effect and returned state belongs to this actual application. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld sourceResult resultCore faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial returned

include receipt heaps stable wellFormed in
/-- Dispatch selects a genuine retained leaf and invokes its original producer
once. A builtin uses its primitive body; user leaves consume strict F only. -/
theorem preserves (budget : Nat)
    (closures : ClosurePreservesBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) functions budget)
    (named : NamedPreservesBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) functions budget)
    {identities : Dynamic.Value → Word → Prop}
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context callerEvidence invocation before function arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (functions := functions) (sourceResult := sourceResult) (resultCore := resultCore)
        initial outcome after value finalStore := by
  cases receipt with
  | closure member represented beforeTyped argumentsTyped locals =>
    obtain ⟨value, finalStore, evaluated, result⟩ :=
      CallableIndexedOwnedPreparedDirectLambdaInvocationBounds.preserves_at
        functions member (bridge.pool initial) represented heaps beforeTyped argumentsTyped locals stable
        wellFormed budget (closures member) called within
    obtain ⟨finalMap, finalWorld, related, finalHeaps, maps, worlds, frame, metadata,
      _reached, _poolRelated, _stable, returned, _samePool, returnedRelated⟩ := result.restore functions bridge initial
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, related, finalHeaps, maps, worlds,
      frame, metadata, returned, returnedRelated⟩
  | named owner member captureZero globals sourceAt capture identity descriptor represented beforeTyped argumentsTyped sameLayouts profiles syntaxTree =>
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, related, finalHeaps, maps, worlds,
      frame, metadata, reached, poolRelated⟩ :=
      CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.application_preserves_at
        functions owner captureZero globals (bridge.pool initial) beforeTyped argumentsTyped stable wellFormed profiles
        syntaxTree sameLayouts member capture represented heaps sourceAt wellFormed.function_ids
        identity descriptor budget (named owner _ member) called within
    obtain ⟨returned, _samePool, returnedRelated⟩ := bridge.restore initial reached maps worlds frame metadata poolRelated
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, related, finalHeaps, maps, worlds,
      frame, metadata, returned, returnedRelated⟩
  | builtin builtin represented invocation =>
    obtain ⟨value, evaluated, related, sameHeap⟩ :=
      CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds.preserves functions observations builtin represented called
    subst after
    exact ⟨value, store, evaluated, mapping, world, related, heaps,
      LocationMap.Extends.refl mapping, WorldExtends.refl world, AdministrativePreserved.refl mapping store,
      Dynamic.HeapMetadataExtend.refl before, initial, callerProtocol.refl initial⟩

include receipt heaps stable wellFormed in
/-- Native application returns an independent Source grade. Each selected
leaf reflects its own body and restores the same original caller exactly once. -/
theorem reflects (budget : Nat)
    (closures : ClosureReflectsBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) functions budget)
    (named : NamedReflectsBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) functions budget)
    {identities : Dynamic.Value → Word → Prop}
    (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues payloads] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context callerEvidence invocation before function arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) (functions := functions) (sourceResult := sourceResult) (resultCore := resultCore)
        initial outcome after value finalStore := by
  cases receipt with
  | closure member represented beforeTyped argumentsTyped locals =>
    obtain ⟨sourceSize, outcome, after, called, result⟩ :=
      CallableIndexedOwnedPreparedDirectLambdaInvocationBounds.reflects_at
        functions member (bridge.pool initial) represented heaps beforeTyped argumentsTyped locals stable
        wellFormed budget (closures member) completed within
    obtain ⟨finalMap, finalWorld, related, finalHeaps, maps, worlds, frame, metadata,
      _reached, _poolRelated, _stable, returned, _samePool, returnedRelated⟩ := result.restore functions bridge initial
    exact ⟨sourceSize, outcome, after, called, finalMap, finalWorld, related, finalHeaps, maps, worlds,
      frame, metadata, returned, returnedRelated⟩
  | named owner member captureZero globals sourceAt capture identity descriptor represented beforeTyped argumentsTyped sameLayouts profiles syntaxTree =>
    obtain ⟨sourceSize, outcome, after, called, finalMap, finalWorld, related, finalHeaps, maps, worlds,
      frame, metadata, reached, poolRelated⟩ :=
      CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.application_reflects_at
        functions owner captureZero globals (bridge.pool initial) beforeTyped argumentsTyped stable wellFormed profiles
        syntaxTree sameLayouts member capture represented heaps sourceAt identity descriptor budget
        (named owner _ member) completed within
    obtain ⟨returned, _samePool, returnedRelated⟩ := bridge.restore initial reached maps worlds frame metadata poolRelated
    exact ⟨sourceSize, outcome, after, called, finalMap, finalWorld, related, finalHeaps, maps, worlds,
      frame, metadata, returned, returnedRelated⟩
  | builtin builtin represented invocation =>
    obtain ⟨sourceSize, outcome, called, related, sameStore⟩ :=
      CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds.reflects functions observations builtin represented completed
    subst finalStore
    exact ⟨sourceSize, outcome, before, called, mapping, world, related, heaps,
      LocationMap.Extends.refl mapping, WorldExtends.refl world, AdministrativePreserved.refl mapping store,
      Dynamic.HeapMetadataExtend.refl before, initial, callerProtocol.refl initial⟩
end Caller
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
