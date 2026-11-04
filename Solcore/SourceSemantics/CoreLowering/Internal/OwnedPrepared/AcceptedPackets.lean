import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryMembers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualStoredCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas

/-!
# Prepared callables: accepted argument packets

Argument packets of accepted builtin, closure and named calls, indirect parent bounds, and the catalog's indirect dispatcher.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds
/-! The actual argument post selects one positive retained application packet.
This adapter builds the original indirect parent's application ports from the
concrete dispatcher and strict body children. The packet factory has no trace,
grade, outcome or execution law input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {evidence invocation : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {canonical : Environment}
  {mapping : LocationMap} {world : StoreTyping} {calleeHeap : Dynamic.Heap} {store : Store}
  {function : Dynamic.Value} {calleeNative : Value}
  {sourceTypes : List TypeSystem.Ty} {sourceResultType : TypeSystem.Ty} {resultCore : Ty}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- An honest contextual packet factory at the admitted argument state. It
retains only the positive closure/global/builtin constructor and raw result
alignment. Each producer must use the same actual carrier and argument list. -/
def ArgumentPackets : Prop :=
  ∀ {middleMap : LocationMap} {middleWorld : StoreTyping} {middle : Dynamic.Heap} {middleStore : Store}
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter sourceResult : TypeSystem.Ty} {packed : Dynamic.Value},
    (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩) →
    Admission bridge context argumentState →
    LocationMap.Extends mapping middleMap → WorldExtends world middleWorld →
    AdministrativePreserved mapping store middleMap middleStore → Dynamic.HeapMetadataExtend calleeHeap middle →
    Dynamic.ValueHasType context calleeHeap function (.function parameter sourceResult) →
    Dynamic.HeapTypesExtend calleeHeap middle →
    DataExpressionSequence.Values model middleMap middleWorld sourceTypes (compiler.codes.map (·.type)) arguments payloads →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions middleMap middleWorld middle middleStore →
    Dynamic.ValuesHaveTypes context middle arguments types → Dynamic.ValuesPack arguments packed →
    TypeSystem.Ty.productMany types = parameter →
    ∃ actualSourceResult,
      SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult ∧
      Receipt (qualification := qualification) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax)
        (mapping := middleMap) (world := middleWorld) (before := middle)
        (arguments := arguments) (payloads := payloads)
        functions function invocation calleeNative actualSourceResult resultCore

private theorem result_at_raw_type {finalMap : LocationMap} {finalWorld : StoreTyping}
    {actualSourceResult : TypeSystem.Ty} {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (same : SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult)
    (related : FunctionCalls.ResultRepresents model finalMap finalWorld actualSourceResult resultCore faults outcome value) :
    FunctionCalls.ResultRepresents model finalMap finalWorld sourceResultType resultCore faults outcome value := by
  cases related with
  | value payload => exact .value (.compatible same payload)
  | fault matched => exact .fault matched

variable (packets : ArgumentPackets (qualification := qualification) (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (context := context) (invocation := invocation) (canonical := canonical)
    (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
    (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
    (sourceResultType := sourceResultType) (resultCore := resultCore) bridge functions compiler)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)

include packets wellFormed observations in
/-- The actual dispatcher constructs the application part of the original
parent from one selected packet and strict F. The argument trace is only a
runtime proof input; it is not retained by the packet factory. -/
theorem preserves (budget : Nat)
    (closures : ClosurePreservesBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) functions budget)
    (named : NamedPreservesBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) functions budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : CallableIndexedOwnedPreparedIndirectValueSourceSuffix.Suffix (Program.ofChecked compiled.sourceProgram)
      context evidence invocation source environment calleeHeap ids function argumentsSize callSize outcome after) :
    CallableIndexedOwnedPreparedIndirectValueParentBounds.ApplicationPreserves
      (registry := registry) (faults := faults) bridge functions compiler
      (context := context) (evidence := evidence) (environment := environment)
      (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := resultCore)
      (sourceResultType := sourceResultType) budget suffix := by
  intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
    argumentState admitted maps worlds frame metadata calleeTyped extension represented heaps
    rawArguments packing bundle argumentsSize callSize outcome after _argumentsTrace called _calledSuffix within
  obtain ⟨actualSourceResult, rawResult, receipt⟩ := packets argumentState admitted maps worlds frame metadata
    calleeTyped extension represented heaps rawArguments packing bundle
  obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, related, finalHeaps, lastMaps, lastWorlds,
      lastFrame, lastMetadata, returned, returnedRelated⟩ :=
    CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.preserves functions bridge argumentState
      heaps admitted.rows wellFormed receipt budget closures named observations called within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result_at_raw_type functions rawResult related,
    finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, returnedRelated⟩

include packets wellFormed observations in
/-- Native reflection constructs its own Source suffix grade and retains the
same reached caller witness. No preservation proof is used in this direction. -/
theorem reflects (budget : Nat)
    (closures : ClosureReflectsBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) functions budget)
    (named : NamedReflectsBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) functions budget) :
    CallableIndexedOwnedPreparedIndirectValueParentBounds.ApplicationReflects
      (registry := registry) (faults := faults) bridge functions compiler
      (context := context) (evidence := evidence) (invocation := invocation)
      (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := resultCore)
      (sourceResultType := sourceResultType) budget := by
  intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
    argumentState admitted maps worlds frame metadata calleeTyped extension represented heaps
    rawArguments packing bundle size value finalStore completed within
  obtain ⟨actualSourceResult, rawResult, receipt⟩ := packets argumentState admitted maps worlds frame metadata
    calleeTyped extension represented heaps rawArguments packing bundle
  obtain ⟨sourceSize, outcome, after, called, finalMap, finalWorld, related, finalHeaps, lastMaps, lastWorlds,
      lastFrame, lastMetadata, returned, returnedRelated⟩ :=
    CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.reflects functions bridge argumentState
      heaps admitted.rows wellFormed receipt budget closures named observations completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, called, result_at_raw_type functions rawResult related,
    finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, returnedRelated⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets
/-! The actual builtin row supplies physical arity at the accepted second gate.
Independent Source and native packed rows then recover the original ordered
builtin arguments. The positive payload retains the authentic builtin carrier;
this construction uses no user body law or supplied application packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {sourceValue : Dynamic.Value} {native : Value} {type : Ty}

private theorem function_builtin
    (positive : FunctionOrigins qualification headers keys bodyRegistry faults profile
      mapping world sourceType sourceValue native type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world sourceType sourceValue native type := by
  cases positive with
  | builtin related =>
    intro function _same
    cases related with
    | prior prior =>
      cases prior with
      | prior original =>
        cases original with
        | builtin builtin => exact builtin
  | closure member => intro function impossible; cases impossible
  | global member => intro function impossible; cases impossible

private theorem builtin_own_type {function : Dynamic.BuiltinFunction}
    (related : CallableIndexedBuiltinValues.Represents compiled.indexed world
      sourceType (.builtin function) native type) :
    CallableIndexedBuiltinValues.Represents compiled.indexed world
      function.id.type (.builtin function) native type := by
  cases related with
  | builtin selected number descriptor typed => exact .builtin selected number descriptor typed

/-- Only the retained builtin branch is inverted. Compatible Source views keep
that same compiler builtin, descriptor and ambient capture environment. -/
theorem builtin_member
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType sourceValue native type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world
        function.id.type (.builtin function) native type := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    intro function same
    cases same
    exact builtin_own_type (function_builtin related function rfl)
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

private theorem builtin_native_type {function : Dynamic.BuiltinFunction}
    (related : CallableIndexedBuiltinValues.Represents compiled.indexed world
      function.id.type (.builtin function) native type) :
    type = CallableContract.functionType (SourceCoreInteger.builtinParameter function.id)
      (SourceCoreInteger.builtinResult function.id) := by
  generalize sourceTypeEq : function.id.type = actualSourceType at related
  cases related
  rfl

private theorem builtin_native_count (function : BuiltinFunctionId) :
    (CompatibleBuiltinMeaning.argumentTypes function).length = function.parameterTypes.length := by
  cases function <;> rfl

private theorem values_represents
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {sourceTypes : List TypeSystem.Ty} {nativeTypes : List Ty}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world sourceTypes nativeTypes arguments payloads) :
    ValuesRep compiled.compatible.checked registry functions mapping world sourceTypes arguments payloads nativeTypes := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

section Arguments
variable {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {calleeHeap before : Dynamic.Heap} {store : Store} {canonical : Environment}
  {function : Dynamic.BuiltinFunction} {invocation : Dynamic.EvidenceEnvironment}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {row : SourceCoreStageCodebook.Decision} {unknown : Word}

local notation "positive" => functions qualification headers keys bodyRegistry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry positive

include compiler in
/-- The authentic selected row supplies physical count before the independent
packed type proofs are used to identify the two ordered argument rows. -/
theorem at_arguments
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt sidecar site
      callee ids metadata compiler.original function native row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown row.entry.id = none)
    {arguments : List Dynamic.Value} {payloads : List Value}
    {parameter result sourceResultType : TypeSystem.Ty}
    (calleeRelated : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType (.builtin function) native compiler.calleeCode.type)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.builtin function) (.function parameter result))
    (represented : DataExpressionSequence.Values model mapping world
      sourceTypes (compiler.codes.map (·.type)) arguments payloads)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (resultSame : sourceResultType = result) :
    ∃ actualSourceResult,
      SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult ∧
      CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.Receipt
        (qualification := qualification) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax)
        (mapping := mapping) (world := world) (before := before)
        (arguments := arguments) (payloads := payloads)
        positive (.builtin function) invocation native actualSourceResult compiler.resultType := by
  have builtin := builtin_member calleeRelated function rfl
  rcases calleeTyped.builtin_inv with ordinary | staged
  · change TypeSystem.Ty.function parameter result =
      TypeSystem.Ty.function (TypeSystem.Ty.productMany function.id.parameterTypes) function.id.returnType at ordinary
    have signature := TypeSystem.Ty.function.inj ordinary
    have nativeSignature : compiler.parameterType = SourceCoreInteger.builtinParameter function.id ∧
        compiler.resultType = SourceCoreInteger.builtinResult function.id := by
      have acceptedType := compiler.callableType
      rw [actualFunctionType] at acceptedType
      exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
        (acceptedType.trans (builtin_native_type builtin))
    have physical : function.id.parameterTypes.length = ids.length :=
      builtinAt.parameter_count.symm.trans
        (CallableIndexedOwnedAcceptedIndirectPhysicalArity.selected_count
          builtinAt.selected builtinAt.selected.found accepted)
    have representedCount : compiler.codes.length = arguments.length := by
      simpa only [List.length_map] using represented.length.1
    have actualCount : arguments.length = function.id.parameterTypes.length :=
      representedCount.symm.trans (compiler.ordered_children.1.symm.trans physical.symm)
    have sourceRow : sourceTypes = function.id.parameterTypes :=
      CallableIndexedOwnedStoredArgumentAlignment.source_rows_of_bundle
        ((CallableIndexedOwnedStoredArgumentAlignment.source_length represented).trans actualCount)
        (sourceBundle.trans signature.1)
    have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
        SourceCoreCompatibleCatalog.packTypes (CompatibleBuiltinMeaning.argumentTypes function.id) :=
      (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
        (compiler.packedType.symm.trans
          (nativeSignature.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function.id).symm))
    have nativeRow : compiler.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function.id :=
      CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
        (represented.length.1.trans (actualCount.trans (builtin_native_count function.id).symm)) nativePacked
    have exactRows := values_represents represented
    rw [sourceRow, nativeRow] at exactRows
    refine ⟨function.id.returnType, congrArg SourceCoreRawMetadata.runtimeType (resultSame.trans signature.2), ?_⟩
    rw [nativeSignature.2]
    exact .builtin builtin exactRows invocation
  · obtain ⟨inner, impossible, _innerTyped⟩ := staged
    cases impossible

include bridge compiler in
/-- Original Source typing, positive builtin provenance and the genuine second
gate construct the full packet factory at every actual admitted argument post. -/
theorem packets
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.builtin function) calleeNode.type)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType (.builtin function) native compiler.calleeCode.type)
    (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt sidecar site
      callee ids metadata compiler.original function native row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown row.entry.id = none) :
    CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .builtin function) (calleeNative := native) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := by
  obtain ⟨sourceParameter, sourceResult, calleeType, _typedRows, sourceBundle, resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler parent tree unique parentTyped calleeFound
  rw [calleeType] at calleeTyped
  rcases calleeTyped.builtin_inv with originalType | staged
  · intro middleMap middleWorld middle middleStore arguments payloads types parameter result packed
      argumentState admitted maps worlds _frame _metadata actualTyped _extension rows _heaps _rawArguments _packing _rawBundle
    rcases actualTyped.builtin_inv with actualType | staged
    · have signature := TypeSystem.Ty.function.inj (originalType.trans actualType.symm)
      exact at_arguments compiler (before := middle) actualFunctionType builtinAt accepted
        (represented.extend (SourceCoreRawMetadata.Extends.refl registry) maps worlds) actualTyped rows
        (sourceBundle.trans signature.1) (resultType.trans signature.2)
    · obtain ⟨inner, impossible, _innerTyped⟩ := staged
      cases impossible
  · obtain ⟨inner, impossible, _innerTyped⟩ := staged
    cases impossible

end Arguments
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinIndirectParentBounds
/-! An authentic builtin row and its two actual gates construct the argument
packet and application parts of the original accepted indirect parent. The
primitive producer runs once, preserves its argument store and Source heap,
and returns the original caller packet. Source and native grades stay separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinIndirectParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
open CallableIndexedOwnedPreparedIndirectValueSourceSuffix (Suffix)
universe u


section Primitive
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
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world before store)
  {arguments : List Dynamic.Value} {payloads : List Value}
  {function : Dynamic.BuiltinFunction} {invocation : Dynamic.EvidenceEnvironment} {native : Value}
  {sourceResult : TypeSystem.Ty} {resultCore : Ty}
  (receipt : Receipt (qualification := qualification) (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (mapping := mapping) (world := world) (before := before) (arguments := arguments) (payloads := payloads)
    functions (.builtin function) invocation native sourceResult resultCore)
  {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)

include receipt heaps observations in
private theorem preserves_builtin_receipt
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context callerEvidence invocation before (.builtin function) arguments outcome after) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (functions := functions)
        (sourceResult := sourceResult) (resultCore := resultCore) initial outcome after value finalStore := by
  cases receipt with
  | builtin builtin represented invocation =>
    obtain ⟨value, evaluated, related, sameHeap⟩ :=
      CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds.preserves functions observations builtin represented called
    subst after
    exact ⟨value, store, evaluated, mapping, world, related, heaps,
      LocationMap.Extends.refl mapping, WorldExtends.refl world, AdministrativePreserved.refl mapping store,
      Dynamic.HeapMetadataExtend.refl before, initial, callerProtocol.refl initial⟩

include receipt heaps observations in
private theorem reflects_builtin_receipt
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues payloads] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context callerEvidence invocation before (.builtin function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) (functions := functions)
        (sourceResult := sourceResult) (resultCore := resultCore) initial outcome after value finalStore := by
  cases receipt with
  | builtin builtin represented invocation =>
    obtain ⟨sourceSize, outcome, called, related, sameStore⟩ :=
      CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds.reflects functions observations builtin represented completed
    subst finalStore
    exact ⟨sourceSize, outcome, before, called, mapping, world, related, heaps,
      LocationMap.Extends.refl mapping, WorldExtends.refl world, AdministrativePreserved.refl mapping store,
      Dynamic.HeapMetadataExtend.refl before, initial, callerProtocol.refl initial⟩

private theorem result_at_raw_type {sourceResultType actualSourceResult : TypeSystem.Ty}
    {resultCore : Ty} {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (same : SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult)
    (related : FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld actualSourceResult resultCore faults outcome value) :
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld sourceResultType resultCore faults outcome value := by
  cases related with
  | value payload => exact .value (.compatible same payload)
  | fault matched => exact .fault matched
end Primitive

private theorem before_arguments
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
    {function : Dynamic.BuiltinFunction} {native : Value} {row : SourceCoreStageCodebook.Decision}
    (receipt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt sidecar site
      callee ids metadata node function native row) (unknown : Word) :
    CallableContract.decision site.gates .beforeArguments unknown row.entry.id = none := by
  rw [site.decision_known .beforeArguments unknown row.entry.id row receipt.selected.found]
  have accepted : row.beforeArguments = .ok () := by
    simp only [SourceCoreStageCodebook.Decision.beforeArguments,
      SourceCoreStageCodebook.Decision.answer, receipt.unguarded]
  exact SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeArguments accepted

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {context : SourceSemantics.Context} {evidence invocation : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  {calleeNode : ExpressionNode} {function : Dynamic.BuiltinFunction} {calleeNative : Value}
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}

section Parent
variable {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {xi : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (parent : SourceParent compiler)
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree xi canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (firstAdmission : Admission bridge context first)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := xi) (calleeNode := calleeNode) (context := context)
    bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler first (.builtin function) calleeHeap calleeNative store mapping world)
  (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt sidecar prepared.site
    callee ids metadata compiler.original function calleeNative row)
  (secondGate : CallableContract.decision prepared.site.gates .beforeApplication
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown row.entry.id = none)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.builtin function) calleeHeap)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) identities)

include certificates expressionSyntax invocation prepared actualFunctionType parent tree unique parentTyped calleeFound wellFormed runtime covers
  environments locals agrees typed firstAdmission post builtinAt secondGate calleeTrace observations
/-- The actual accepted builtin parent uses only its measured ordered expression
children. The primitive application has no body family premise. -/
theorem preserves (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile)) context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment
      calleeHeap ids (.builtin function) argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename xi) value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, metadata, reached, related, admission⟩ := post
  have calleeTyped := admission.at_value.1
  have packets : CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .builtin function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler :=
    CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets.packets bridge compiler
      actualFunctionType parent tree unique parentTyped calleeFound calleeTyped represented builtinAt secondGate
  have firstGate := before_arguments builtinAt
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  obtain ⟨raw, shape⟩ := builtinAt.shape
  have callable : Dynamic.CallableValue (.builtin function) := by simp only [Dynamic.CallableValue]
  have nativeTyped := represented.runtime_hasType
  have signature := compiler.callableType
  rw [actualFunctionType] at signature
  rw [← signature] at nativeTyped
  have application : CallableIndexedOwnedPreparedIndirectValueParentBounds.ApplicationPreserves
      (registry := registry) (faults := faults) bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler
      (context := context) (evidence := evidence) (environment := environment)
      (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := .builtin function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := compiler.resultType)
      (sourceResultType := compiler.original.type) budget suffix := by
    intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
      argumentState admitted maps worlds frame metadata calleeTyped extension represented heaps
      rawArguments packing bundle argumentsSize callSize outcome after _argumentsTrace called _calledSuffix _within
    obtain ⟨actualSourceResult, rawResult, receipt⟩ := packets argumentState admitted maps worlds frame metadata
      calleeTyped extension represented heaps rawArguments packing bundle
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, related, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, returned, returnedRelated⟩ :=
      preserves_builtin_receipt (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) argumentState heaps receipt observations called
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result_at_raw_type (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) rawResult related,
      finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, returnedRelated⟩
  exact CallableIndexedOwnedPreparedIndirectValueParentBounds.preserves_with_application bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler prepared
    parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed first firstAdmission
    reached related maps worlds frame metadata callable nativeTyped heaps rfl rfl
    shape firstGate secondGate calleeTrace calleeEvaluation builtinAt.selected budget children suffix
    argumentsWithin callWithin application

include certificates expressionSyntax invocation prepared actualFunctionType parent tree unique parentTyped calleeFound wellFormed runtime covers
  environments locals agrees typed firstAdmission post builtinAt secondGate calleeTrace observations
/-- Reflection consumes the literal original native completion. Its own Source
suffix grade and returned caller witness come from the original parent inversion. -/
theorem reflects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile)) context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename xi) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, metadata, reached, related, admission⟩ := post
  have calleeTyped := admission.at_value.1
  have packets : CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .builtin function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler :=
    CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets.packets bridge compiler
      actualFunctionType parent tree unique parentTyped calleeFound calleeTyped represented builtinAt secondGate
  have firstGate := before_arguments builtinAt
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  obtain ⟨raw, shape⟩ := builtinAt.shape
  have callable : Dynamic.CallableValue (.builtin function) := by simp only [Dynamic.CallableValue]
  have nativeTyped := represented.runtime_hasType
  have signature := compiler.callableType
  rw [actualFunctionType] at signature
  rw [← signature] at nativeTyped
  have application : CallableIndexedOwnedPreparedIndirectValueParentBounds.ApplicationReflects
      (registry := registry) (faults := faults) bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler
      (context := context) (evidence := evidence) (invocation := invocation)
      (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := .builtin function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := compiler.resultType)
      (sourceResultType := compiler.original.type) budget := by
    intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
      argumentState admitted maps worlds frame metadata calleeTyped extension represented heaps
      rawArguments packing bundle size value finalStore completed _within
    obtain ⟨actualSourceResult, rawResult, receipt⟩ := packets argumentState admitted maps worlds frame metadata
      calleeTyped extension represented heaps rawArguments packing bundle
    obtain ⟨sourceSize, outcome, after, called, finalMap, finalWorld, related, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, returned, returnedRelated⟩ :=
      reflects_builtin_receipt (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) argumentState heaps receipt observations completed
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, called, result_at_raw_type (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) rawResult related,
      finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, returnedRelated⟩
  exact CallableIndexedOwnedPreparedIndirectValueParentBounds.reflects_with_application bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler prepared
    unique parentTyped first reached parent tree wellFormed runtime covers environments locals agrees typed firstAdmission
    related maps worlds frame metadata nativeTyped heaps rfl rfl callable
    shape firstGate secondGate calleeTrace calleeEvaluation builtinAt.selected budget children application completed within

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinIndirectParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts
/-! The actual admitted argument post supplies independent Source heap and
argument typing. These constructors combine that typing with the genuine
retained closure or global compiler leaf. No flow, body meaning or execution
outcome is an input to the application receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedSourceAt NamedCapture)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (Association)
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher (Receipt)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {context : SourceSemantics.Context} {source : TypedSource}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
  (admitted : Admission bridge context initial)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  {calleeHeap : Dynamic.Heap} {arguments : List Dynamic.Value} {payloads : List Value}
  {types : List TypeSystem.Ty} {parameter result : TypeSystem.Ty} {packed : Dynamic.Value}
  (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
  (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap arguments types)
  (packing : Dynamic.ValuesPack arguments packed)
  (bundle : TypeSystem.Ty.productMany types = parameter)

include bridge initial admitted runtime extension argumentsTyped packing bundle in
/-- Raw Source closure admission is reconstructed at this actual argument
heap, after its genuine Source type extension. The stored Code is unchanged. -/
theorem closure {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
    (member : Association qualification headers keys bodyRegistry faults
      index.mapping index.world function native bindings parameterCore resultCore)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      index.mapping index.world bindings arguments payloads) :
    Receipt (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (mapping := index.mapping) (world := index.world) (before := index.heap) (arguments := arguments) (payloads := payloads)
      functions (.closure function) function.evidence native function.resultType resultCore := by
  have count : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length member.source_binders
  have arity : arguments.length = function.parameters.length := represented.length.1.symm.trans count
  obtain ⟨raw, _rows⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    bridge initial runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  exact .closure member represented raw.heaps raw.arguments raw.captures

include bridge initial admitted runtime extension argumentsTyped packing bundle in
/-- The genuine global SourceFrame and dictionary transport the packed raw
argument typing into the retained Header context at the same reached heap. -/
theorem named {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
    (owner : OwnedKey keys) (member : header ∈ headers)
    (captureZero : owner.key.capturePrefix = 0)
    (globals : header.globals = compiled.indexed.base.globals.length)
    (sourceAt : NamedSourceAt header rawD function)
    (capture : NamedCapture headers owner.key header index.mapping index.world)
    (identity descriptor : Word) (sameLayouts : header.layouts = compiled.indexed.layouts)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      index.mapping index.world header.bindings arguments payloads)
    (profiles : CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions owner (header := header))
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType) :
    Receipt (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (mapping := index.mapping) (world := index.world) (before := index.heap) (arguments := arguments) (payloads := payloads)
      functions (.global function) function.evidence
      (CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.carrier owner capture identity descriptor)
      header.function.resultType header.output := by
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have packedTyped : Dynamic.ValueHasType context index.heap packed parameter :=
    bundle ▸ packing.hasType argumentsTyped
  obtain ⟨heapTyped, rawTyped⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.arguments_at_global
      sourceAt wellFormed runtime admitted.heap (calleeTyped.mono extension) packing packedTyped arity
  exact .named owner member captureZero globals sourceAt capture identity descriptor represented
    heapTyped rawTyped sameLayouts profiles syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveClosureArgumentReceipts
/-! An accepted indirect closure call reconstructs its application packet at
the actual argument post. The positive callee supplies the genuine selected
compiler association. Source typing supplies its raw signature, while the
accepted physical count remains an independent input. Neither a body execution
law nor an application receipt is an input to this producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveClosureArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
  {context : SourceSemantics.Context} (admitted : Admission bridge context initial)
  {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  {calleeHeap : Dynamic.Heap} {function : Dynamic.Closure} {native : Value}
  {sourceTypes types : List TypeSystem.Ty} {arguments : List Dynamic.Value} {payloads : List Value}
  {parameter result sourceResultType : TypeSystem.Ty} {packed : Dynamic.Value}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)

local notation "positive" => functions qualification headers keys bodyRegistry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry positive

include compiler bridge initial admitted runtime in
/-- Both ordered argument rows are derived independently. The original typed
closure argument producer is then called once at this same reached state. -/
theorem closure_at_arguments
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    {calleeType : TypeSystem.Ty}
    (calleeRelated : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      index.mapping index.world calleeType (.closure function) native compiler.calleeCode.type)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
    (represented : DataExpressionSequence.Values model index.mapping index.world
      sourceTypes (compiler.codes.map (·.type)) arguments payloads)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (physicalArity : arguments.length = function.parameters.length)
    (rawArguments : Dynamic.ValuesHaveTypes context index.heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (rawBundle : TypeSystem.Ty.productMany types = parameter)
    (resultSame : sourceResultType = result) :
    ∃ actualSourceResult,
      SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult ∧
      CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.Receipt
        (qualification := qualification) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax)
        (mapping := index.mapping) (world := index.world) (before := index.heap)
        (arguments := arguments) (payloads := payloads)
        positive (.closure function) function.evidence native actualSourceResult compiler.resultType := by
  obtain ⟨bindings, parameterCore, resultCore, ⟨packet⟩, _nativeType⟩ :=
    closure_member calleeRelated function rfl
  let association := packet.association
  have rawSignature := Dynamic.ValueHasType.closure_function_inv calleeTyped
  have compilerSignature : compiler.parameterType = parameterCore ∧ compiler.resultType = resultCore := by
    have accepted := compiler.callableType
    rw [actualFunctionType] at accepted
    exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
      (accepted.trans (calleeRelated.runtime_hasType.type_eq.symm.trans association.native_type))
  have bindingCount : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length association.source_binders
  have sourcePacked : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) :=
    sourceBundle.trans (rawSignature.1.trans (congrArg TypeSystem.Ty.productMany association.source_binders).symm)
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans (compilerSignature.1.trans (association.parameter_core profile)))
  have binderArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    bindings represented (physicalArity.trans bindingCount.symm) sourcePacked nativePacked
  refine ⟨function.resultType, congrArg SourceCoreRawMetadata.runtimeType (resultSame.trans rawSignature.2.1), ?_⟩
  rw [compilerSignature.2]
  exact CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts.closure positive bridge initial
    admitted runtime extension rawArguments packing rawBundle association calleeTyped binderArguments

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveClosureArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedClosureArgumentPackets
/-! The actual selected closure and accepted application gate construct the
indirect parent's argument factory. Ordered compiler and represented rows fix
physical arity. Original Source typing fixes the raw argument and result types.
No argument trace, body meaning or application law is retained by this factory. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedClosureArgumentPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {calleeHeap : Dynamic.Heap} {store : Store}
  {function : Dynamic.Closure} {native : Value} {canonical : Environment}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {unknown : Word} {sourceType : TypeSystem.Ty}

local notation "positive" => functions qualification headers keys bodyRegistry faults profile

include bridge compiler in
/-- The same selected descriptor and original Source parent close the factory
at every genuine admitted argument post. All body callbacks remain outside it. -/
theorem packets
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) calleeNode.type)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType (.closure function) native compiler.calleeCode.type)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.closure function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata
      compiler.original dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none) :
    CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := function.evidence) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .closure function) (calleeNative := native) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := by
  obtain ⟨sourceParameter, sourceResult, calleeType, _typedRows, sourceBundle, resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler parent tree unique parentTyped calleeFound
  rw [calleeType] at calleeTyped
  have originalSignature := Dynamic.ValueHasType.closure_function_inv calleeTyped
  have physical := CallableIndexedOwnedAcceptedIndirectPhysicalArity.closure_count dispatch selected accepted
  intro middleMap middleWorld middle middleStore arguments payloads types parameter result packed
    argumentState admitted maps worlds _frame _metadata actualTyped extension rows _heaps rawArguments packing rawBundle
  have actualSignature := Dynamic.ValueHasType.closure_function_inv actualTyped
  have actualBundle : TypeSystem.Ty.productMany sourceTypes = parameter :=
    sourceBundle.trans (originalSignature.1.trans actualSignature.1.symm)
  have resultSame : compiler.original.type = result :=
    resultType.trans (originalSignature.2.1.trans actualSignature.2.1.symm)
  have argumentCount : arguments.length = function.parameters.length := by
    have ordered := compiler.ordered_children.1
    have representedCount : compiler.codes.length = arguments.length := by
      simpa only [List.length_map] using rows.length.1
    exact representedCount.symm.trans (ordered.symm.trans physical.symm)
  exact CallableIndexedOwnedPreparedPositiveClosureArgumentReceipts.closure_at_arguments
    bridge argumentState admitted runtime compiler actualFunctionType
    (represented.extend (SourceCoreRawMetadata.Extends.refl registry) maps worlds) actualTyped extension rows actualBundle argumentCount
    rawArguments packing rawBundle resultSame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedClosureArgumentPackets
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets
/-! Accepted named application retains the actual positive named association.
Its Source frame fixes the raw signature and ordered binders. The selected
second gate fixes physical arity separately, while the compiler fixes the
native bundle. Static body profiles remain independent of execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {calleeHeap : Dynamic.Heap} {store : Store}
  {function : Dynamic.GlobalFunction} {native : Value} {canonical : Environment}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {unknown : Word} {sourceType : TypeSystem.Ty}

local notation "positive" => functions qualification headers keys bodyRegistry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry positive

/-- These are finite static compiler profiles for the actual owned headers.
They contain no Source trace, native execution or body meaning premise. -/
structure StaticBodies where
  layouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts
  profiles : ∀ (origin : Owner (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (profile := profile))
      (header : Header compiled (Program.ofChecked compiled.sourceProgram)), header ∈ headers →
    CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      positive origin.owner (header := header)
  syntaxTree : ∀ header, header ∈ headers →
    GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType

include bridge compiler in
/-- Construct the named application packet once at the actual argument state.
The positive association supplies the same complete Source dictionary and
capture; neither is reconstructed from an erased function relation. -/
theorem at_arguments
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (static : StaticBodies (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (profile := profile)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (faults := faults))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata
      compiler.original dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none)
    {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
    (admitted : Admission bridge context initial)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter result sourceResultType : TypeSystem.Ty} {packed : Dynamic.Value}
    (calleeRelated : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      index.mapping index.world sourceType (.global function) native compiler.calleeCode.type)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
    (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
    (represented : DataExpressionSequence.Values model index.mapping index.world
      sourceTypes (compiler.codes.map (·.type)) arguments payloads)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (rawArguments : Dynamic.ValuesHaveTypes context index.heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (rawBundle : TypeSystem.Ty.productMany types = parameter)
    (resultSame : sourceResultType = result) :
    ∃ actualSourceResult,
      SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult ∧
      CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.Receipt
        (qualification := qualification) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax)
        (mapping := index.mapping) (world := index.world) (before := index.heap)
        (arguments := arguments) (payloads := payloads)
        positive (.global function) function.evidence native actualSourceResult compiler.resultType := by
  obtain ⟨actualType, _sameType, ⟨packet⟩⟩ := global_member calleeRelated function rfl
  generalize compilerType : compiler.calleeCode.type = nativeType at packet
  cases packet with
  | @named header rawD source identity origin member sourceAt capture installed number projection descriptor typed =>
    rcases calleeTyped.global_inv with ordinary | staged
    · obtain ⟨typeEq, _valid, _evidence⟩ := ordinary
      obtain ⟨facts, certified⟩ :=
        CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
      have signature := TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)
      have bindingTypes : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
        have bodyTypes := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
        rw [header.parameters] at bodyTypes
        simpa only [List.map_map, Function.comp_def] using bodyTypes.symm
      have nativeSignature : compiler.parameterType = header.named.signature.parameterType ∧
          compiler.resultType = header.named.signature.resultType := by
        have acceptedType := compiler.callableType
        rw [actualFunctionType] at acceptedType
        exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (acceptedType.trans compilerType)
      have physical := CallableIndexedOwnedAcceptedIndirectPhysicalArity.named_count sourceAt caller dispatch selected accepted
      have ordered := compiler.ordered_children.1
      have representedCount : compiler.codes.length = arguments.length := by
        simpa only [List.length_map] using represented.length.1
      have actualCount : arguments.length = header.bindings.length := by
        have parameterCount : header.function.parameters.length = header.bindings.length := by
          simpa only [List.length_map] using congrArg List.length header.parameters
        exact representedCount.symm.trans (ordered.symm.trans (physical.symm.trans parameterCount))
      have sourcePacked := sourceBundle.trans (signature.1.trans (congrArg TypeSystem.Ty.productMany bindingTypes))
      have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
          SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :=
        (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
          (compiler.packedType.symm.trans (nativeSignature.1.trans header.parameterType))
      have binderArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
        header.bindings represented actualCount sourcePacked nativePacked
      refine ⟨header.function.resultType,
        congrArg SourceCoreRawMetadata.runtimeType (resultSame.trans (signature.2.trans sourceAt.frame.result.symm)), ?_⟩
      rw [nativeSignature.2, header.resultType]
      simpa only [CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.carrier, header.resultType] using
        (CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts.named positive bridge initial admitted runtime
        extension rawArguments packing rawBundle origin.owner member origin.capture_zero (origin.globals member)
        sourceAt capture identity descriptor.id (static.layouts header member) wellFormed calleeTyped
        binderArguments (static.profiles origin header member) (static.syntaxTree header member))
    · obtain ⟨inner, impossible, _innerTyped⟩ := staged
      cases impossible

include bridge compiler in
/-- Original Source typing and the actual accepted selected row construct the
full named argument factory with the original invocation and result indices. -/
theorem packets
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (static : StaticBodies (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (profile := profile)
      (certificates := certificates) (expressionSyntax := expressionSyntax) (faults := faults))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) calleeNode.type)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType (.global function) native compiler.calleeCode.type)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar site callee ids metadata
      compiler.original dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none) :
    CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := function.evidence) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .global function) (calleeNative := native) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := by
  obtain ⟨sourceParameter, sourceResult, calleeType, _typedRows, sourceBundle, resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler parent tree unique parentTyped calleeFound
  rw [calleeType] at calleeTyped
  rcases calleeTyped.global_inv with ordinary | staged
  · obtain ⟨originalType, _valid, _evidence⟩ := ordinary
    intro middleMap middleWorld middle middleStore arguments payloads types parameter result packed
      argumentState admitted maps worlds _frame _metadata actualTyped extension rows _heaps rawArguments packing rawBundle
    rcases actualTyped.global_inv with actual | staged
    · obtain ⟨actualType, _actualValid, _actualEvidence⟩ := actual
      have signature := TypeSystem.Ty.function.inj (originalType.trans actualType.symm)
      exact at_arguments bridge compiler actualFunctionType static wellFormed caller dispatch selected accepted
        argumentState admitted runtime
        (represented.extend (SourceCoreRawMetadata.Extends.refl registry) maps worlds) actualTyped extension rows
        (sourceBundle.trans signature.1) rawArguments packing rawBundle (resultType.trans signature.2)
    · obtain ⟨inner, impossible, _innerTyped⟩ := staged
      cases impossible
  · obtain ⟨inner, impossible, _innerTyped⟩ := staged
    cases impossible

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedUserIndirectParentBounds
/-! Actual accepted user calls select their argument factory from the literal
closure or named callee. The whole parent consumes that factory and strict body
children through the original dispatcher. Its callee and argument posts, Source
and native grades, and returned caller state remain separate and unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedUserIndirectParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
open CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds (ArgumentPackets)
open CallableIndexedOwnedPreparedIndirectValueSourceSuffix (Suffix)
universe u

/-- The actual user callee fixes its complete invocation dictionary. -/
inductive UserCallee : Dynamic.Value → Dynamic.EvidenceEnvironment → Prop where
  | closure (function : Dynamic.Closure) : UserCallee (.closure function) function.evidence
  | global (function : Dynamic.GlobalFunction) : UserCallee (.global function) function.evidence

private theorem UserCallee.callable {function invocation} (user : UserCallee function invocation) :
    Dynamic.CallableValue function := by
  cases user <;> simp only [Dynamic.CallableValue]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {context : SourceSemantics.Context} {evidence invocation : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  {calleeNode : ExpressionNode} {function : Dynamic.Value} {calleeNative : Value}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "positive" => functions qualification headers keys bodyRegistry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry positive
local notation "namedBodies" => CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets.StaticBodies
  (qualification := qualification) (headers := headers) (keys := keys)
  (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (profile := profile)
  (certificates := certificates) (expressionSyntax := expressionSyntax)

section Packets
variable {mapping : LocationMap} {world : StoreTyping} {calleeHeap : Dynamic.Heap} {store : Store}
  {canonical : Environment}

include bridge compiler prepared in
/-- Both user alternatives construct their factory from original Source typing,
the same selected row and accepted gate. No application or argument law is an input. -/
theorem user_packets
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (static : namedBodies)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (user : UserCallee function invocation)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap function calleeNode.type)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world calleeNode.type function calleeNative compiler.calleeCode.type)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      prepared.site prepared.site.call ids function calleeNative)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
      compiler.original dispatch.row)
    (accepted : CallableContract.decision prepared.site.gates .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none) :
    ArgumentPackets (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := by
  cases user with
  | closure function =>
    exact CallableIndexedOwnedPreparedAcceptedClosureArgumentPackets.packets bridge compiler
      actualFunctionType parent tree unique parentTyped calleeFound runtime calleeTyped represented dispatch selected accepted
  | global function =>
    exact CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets.packets bridge compiler
      actualFunctionType static wellFormed parent tree unique parentTyped calleeFound runtime
      calleeTyped represented caller dispatch selected accepted

end Packets

section Parent
variable {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {xi : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (static : CallableIndexedOwnedPreparedAcceptedNamedArgumentPackets.StaticBodies
    (qualification := qualification) (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (profile := profile)
    (certificates := certificates) (expressionSyntax := expressionSyntax))
  (parent : SourceParent compiler)
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree xi canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (firstAdmission : Admission bridge context first)
  (user : UserCallee function invocation)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := xi) (calleeNode := calleeNode) (context := context)
    bridge (functions qualification headers keys bodyRegistry faults profile) compiler first function calleeHeap calleeNative store mapping world)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
    prepared.site prepared.site.call ids function calleeNative)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
    compiler.original dispatch.row)
  (stageAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
    prepared.site.call ids function)
  (secondGate : CallableContract.decision prepared.site.gates .beforeApplication
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee function calleeHeap)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (functions qualification headers keys bodyRegistry faults profile) identities)

include prepared actualFunctionType static parent tree unique parentTyped calleeFound wellFormed runtime covers
  environments locals agrees typed firstAdmission user post caller dispatch selected stageAccepted secondGate calleeTrace observations
/-- The original whole accepted parent consumes the actual callee and argument
posts and the strict body family. Source and native grades remain independent. -/
theorem preserves (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    (closures : ClosurePreservesBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) positive budget)
    (named : NamedPreservesBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) positive budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment
      calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename xi) value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge positive compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, metadata, reached, related, admission⟩ := post
  have calleeTyped := admission.at_value.1
  have packets : ArgumentPackets (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := user_packets bridge compiler prepared actualFunctionType static wellFormed
    parent tree unique parentTyped calleeFound runtime user calleeTyped represented caller dispatch selected secondGate
  have firstGate := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch stageAccepted
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  have nativeTyped := represented.runtime_hasType
  have signature := compiler.callableType
  rw [actualFunctionType] at signature
  rw [← signature] at nativeTyped
  exact CallableIndexedOwnedPreparedIndirectValueParentBounds.preserves_with_application bridge positive compiler prepared
    parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed first firstAdmission
    reached related maps worlds frame metadata user.callable nativeTyped heaps rfl rfl
    dispatch.shape firstGate secondGate calleeTrace calleeEvaluation selected budget children suffix
    argumentsWithin callWithin (CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.preserves
      bridge positive compiler packets wellFormed observations budget closures named suffix)

include prepared actualFunctionType static parent tree unique parentTyped calleeFound wellFormed runtime covers
  environments locals agrees typed firstAdmission user post caller dispatch selected stageAccepted secondGate calleeTrace observations
/-- Reflection consumes the literal original native completion. Its own Source
suffix grade and returned caller witness come from the original parent inversion. -/
theorem reflects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (closures : ClosureReflectsBelow (qualification := qualification) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) positive budget)
    (named : NamedReflectsBelow (headers := headers) (keys := keys) (registry := registry)
      (faults := faults) (certificates := certificates) (expressionSyntax := expressionSyntax) positive budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename xi) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge positive compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, metadata, reached, related, admission⟩ := post
  have calleeTyped := admission.at_value.1
  have packets : ArgumentPackets (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := user_packets bridge compiler prepared actualFunctionType static wellFormed
    parent tree unique parentTyped calleeFound runtime user calleeTyped represented caller dispatch selected secondGate
  have firstGate := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch stageAccepted
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  have nativeTyped := represented.runtime_hasType
  have signature := compiler.callableType
  rw [actualFunctionType] at signature
  rw [← signature] at nativeTyped
  exact CallableIndexedOwnedPreparedIndirectValueParentBounds.reflects_with_application bridge positive compiler prepared
    unique parentTyped first reached parent tree wellFormed runtime covers environments locals agrees typed firstAdmission
    related maps worlds frame metadata nativeTyped heaps rfl rfl user.callable
    dispatch.shape firstGate secondGate calleeTrace calleeEvaluation selected budget children
    (CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.reflects
      bridge positive compiler packets wellFormed observations budget closures named) completed within

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedUserIndirectParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalLambdaBodySupport
/-! The actual lexical lambda callback builds a static body certificate.
Children retain their original typed nodes; application meaning is supplied
later by the recursive body family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)

def Syntax : TypedSource → ExpressionId → Prop := fun _ _ => True

def Child : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ source context _ id _ => ∃ node,
    source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Every tree node is recovered from the accepted same-view compiler flow and
independent Source syntax at the real parameter context. -/
theorem of_lexical
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (view : code.view = function.source)
    (owner : code.compilation.owner = named.signature.key)
    (active : code.active = [])
    (onError : code.allocationError = fun error => .sourceAllocation (reprStr error))
    (signatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) inputs.context)
    (syntaxTree : GenericLexicalStatements.Syntax function.source (Syntax function.source)
      inputs.context true function.body function.resultType) :
    ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) Syntax Child code
      (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs ∧ GenericImperativeMatch.Syntax function.source (Syntax function.source)
        body.context (.statements true function.body) function.resultType := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    (congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe).trans
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
        compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := CompatibleEncoding.bind_ok accepted
  have emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
      code.compilation.internalReason code.compilation.internalReason := (Except.ok.inj returned).symm
  have native := CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native code
  rw [emitted] at native
  obtain ⟨nativeType, native⟩ := TypedLexicalWhile.Native.finished_flow native
  have projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections code profile).2
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have generatedSource : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow := by
    simpa only [view] using generated
  have binderPolicy : ∀ current binder, binder.scheme.quantified = [] →
      policy.lowerBinder function.source current binder =
        SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked function.source current binder := by
    intro current binder mono
    change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
    simp only [SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte]
    rfl
  have allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      (compiled.indexed.layouts.allocatorAt code.compilation.owner code.active code.allocationError)) := by
    rw [owner, active, onError]
    rfl
  let tree := CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual
    (values := .initial compiled.compatible.checked) true
    (show policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked from rfl)
    binderPolicy allocationPolicy
    (certificates := Child 0 function.source)
    (fun context _closed _residual _signatures scope fuel id node lowered _declarations _syntax found typed _accepted nativeType _native =>
      ⟨node, found, typed⟩)
    syntaxTree runtime.variables_closed runtime.residual_variables_open signatures declarations projection generatedSource native
  let full : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) function.source (Syntax function.source) (Child 0 function.source)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow := .body syntaxTree tree
  have sites : full.CatalogSites .reachable registry faults := .body (syntaxTree := syntaxTree) (body := tree)
  let actualTree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) code.view (Syntax code.view) (Child 0 code.view)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow := by
    simpa only [view] using full
  have actualSites : actualTree.CatalogSites .reachable registry faults := by
    simpa only [view] using sites
  refine ⟨{
    toContext := inputs, frame := frame, readFuel := 0, policy := policy, callback := callback
    flow := flow, generated := generated, projection := projection, emitted := emitted
    actualTree := actualTree, actualSites := actualSites, tree := full, sites := sites
    valid := CallableIndexedLambdaStaticBodySupport.context_valid (values := .initial compiled.compatible.checked) code inputs frame sameLedger
    unique := frame.code.graph.nodeOccurrencesUnique }, rfl, .body syntaxTree⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalLambdaBodySupport
end
