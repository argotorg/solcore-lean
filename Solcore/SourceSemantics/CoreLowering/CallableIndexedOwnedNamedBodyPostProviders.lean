import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedParameterReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrimitiveNamedBodyFaultBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSequentialNamedBodyFaultBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds

/-! The actual successful argument and parameter receipts supply concrete
singleton/sequential body posts. The outer named/direct core consumes them
once and retains its full call route at the same returned caller tuple. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyPostProviders
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
open RecursiveNamedBoundedContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The exact singleton emission and pointwise primitive diagnostic receipts. -/
structure PrimitiveInputs (header : CallableIndexedOwnedFunctionValues.Header compiled program) where
  statement : StatementId
  node : StatementNode
  expression : ExpressionId
  expressionNode : ExpressionNode
  fuel : Nat
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  lowered : SourceCoreBasic.LoweredExpr
  fellThrough : Word
  escaped : Word
  singleton : ReachedNamedPrimitiveBodyFaultPaths.SingletonAt (.initial compiled.compatible.checked)
    header.function header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    statement node expression expressionNode fuel solved reasonAt lowered header.body fellThrough escaped
  output : lowered.type = header.output
  valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence
  reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults
  missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults
  unique : NodeOccurrencesUnique header.function.source

/-- The actual first discard and its literal singleton suffix at the same Header. -/
structure SequentialInputs (header : CallableIndexedOwnedFunctionValues.Header compiled program) where
  statement : StatementId
  node : StatementNode
  expression : ExpressionId
  expressionNode : ExpressionNode
  fuel : Nat
  last : StatementId
  lastNode : StatementNode
  lastExpression : ExpressionId
  lastExpressionNode : ExpressionNode
  lastFuel : Nat
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  lowered : SourceCoreBasic.LoweredExpr
  lastLowered : SourceCoreBasic.LoweredExpr
  fellThrough : Word
  escaped : Word
  sequential : ReachedNamedSequentialBodyFaultPaths.SequentialAt (.initial compiled.compatible.checked)
    header.function header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    statement node expression expressionNode fuel last lastNode lastExpression lastExpressionNode lastFuel
    solved reasonAt lowered lastLowered header.body fellThrough escaped
  output : lastLowered.type = header.output
  valid : CompatibleExpressionLiterals.ContextValid solved header.context header.function.evidence
  reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults
  lastReads : ReachedLoweredReadOutcomePorts.ReadPolicies lastFuel (.initial compiled.compatible.checked)
    header.function.source header.context reasonAt faults
  missing : IndexFaultPostContracts.MissingPolicies (.initial compiled.compatible.checked)
    header.function.source functions registry program header.context header.function.evidence reasonAt faults
  unique : NodeOccurrencesUnique header.function.source

/-- A genuine static domain selects a concrete producer, never a completed body law. -/
inductive BodyInputs (header : CallableIndexedOwnedFunctionValues.Header compiled program) : Prop where
  | primitive (inputs : PrimitiveInputs (program := program) (registry := registry) (faults := faults) functions header) : BodyInputs header
  | sequential (inputs : SequentialInputs (program := program) (registry := registry) (faults := faults) functions header) : BodyInputs header

/-- Both concrete paths retain their original complete literal body post. -/
def FaultPost : BodyFaultPost := fun program function context environment before actual initialStore body
    reason after token mapping world store =>
  ReachedNamedPrimitiveBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry
    program function context environment before actual initialStore body reason after token mapping world store ∨
  ReachedNamedSequentialBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry
    program function context environment before actual initialStore body reason after token mapping world store

section Body
variable {functions}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {locations : RecursiveNamedCatalog.Locations} {capturePrefix : Nat}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
  (reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
    entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
  (source : SourceReceipt program header.function header.context entry.environment entry.heap)
  (rows : StableRows reached)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed program)

include source rows extension faithful observations functionTypes wellFormed in
/-- The concrete source child runs its selected existing producer once. -/
theorem BodyInputs.source_below (inputs : BodyInputs (program := program) (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) := by
  cases inputs with
  | primitive inputs =>
    intro child _strict
    intro outcome after trace
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, result, finalHeaps,
      maps, worlds, frame, metadata, returned, retained⟩ :=
      CallableIndexedOwnedPrimitiveNamedBodyFaultBounds.source_body_with_post
        functions entry reached inputs.singleton inputs.output source rows extension faithful observations functionTypes
        inputs.valid inputs.reads inputs.missing inputs.unique wellFormed child trace
    refine ⟨value, finalStore, finalMap, finalWorld, completed, result, finalHeaps,
      maps, worlds, frame, metadata, returned, ?_⟩
    cases outcome with
    | value value => trivial
    | fault reason =>
      obtain ⟨token, same, post⟩ := retained
      exact ⟨token, same, Or.inl post⟩

  | sequential inputs =>
    intro child _strict
    intro outcome after trace
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, result, finalHeaps,
      maps, worlds, frame, metadata, returned, retained⟩ :=
      CallableIndexedOwnedSequentialNamedBodyFaultBounds.source_body_with_post
        functions entry reached inputs.sequential inputs.output source rows extension faithful observations functionTypes
        inputs.valid inputs.reads inputs.lastReads inputs.missing inputs.unique wellFormed child trace
    refine ⟨value, finalStore, finalMap, finalWorld, completed, result, finalHeaps,
      maps, worlds, frame, metadata, returned, ?_⟩
    cases outcome with
    | value value => trivial
    | fault reason =>
      obtain ⟨token, same, post⟩ := retained
      exact ⟨token, same, Or.inr post⟩

include source rows extension faithful observations functionTypes wellFormed in
/-- The concrete native child runs its selected existing producer once. -/
theorem BodyInputs.native_below (inputs : BodyInputs (program := program) (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) := by
  cases inputs with
  | primitive inputs =>
    intro child _strict
    intro value finalStore completed
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned, retained⟩ :=
      CallableIndexedOwnedPrimitiveNamedBodyFaultBounds.native_body_with_post
        functions entry reached inputs.singleton inputs.output source rows extension faithful observations functionTypes
        inputs.valid inputs.reads inputs.missing inputs.unique wellFormed child completed
    refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned, ?_⟩
    cases outcome with
    | value value => trivial
    | fault reason =>
      obtain ⟨token, same, post⟩ := retained
      exact ⟨token, same, Or.inl post⟩

  | sequential inputs =>
    intro child _strict
    intro value finalStore completed
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned, retained⟩ :=
      CallableIndexedOwnedSequentialNamedBodyFaultBounds.native_body_with_post
        functions entry reached inputs.sequential inputs.output source rows extension faithful observations functionTypes
        inputs.valid inputs.reads inputs.lastReads inputs.missing inputs.unique wellFormed child completed
    refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps,
      maps, worlds, frame, metadata, returned, ?_⟩
    cases outcome with
    | value value => trivial
    | fault reason =>
      obtain ⟨token, same, post⟩ := retained
      exact ⟨token, same, Or.inr post⟩

end Body

section Providers
variable {functions}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {callerPrefix : Nat} {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner callerPrefix index.scope index.canonical) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical : Environment} {environment : Dynamic.Environment}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots bridge) context initial)
  {originalTypes : List TypeSystem.Ty} {rawResult : TypeSystem.Ty} {predicates : List ProgramPredicate}
  (wellFormed : ProgramWellFormed program)
  (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (argumentTypes : ExpressionsHaveTypes source context ids originalTypes)
  (application : SourceSemantics.DeclarationApplicationValid context header.instantiation originalTypes rawResult predicates)
  (inputs : BodyInputs (program := program) (registry := registry) (faults := faults) functions header)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs extension faithful observations functionTypes in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem source_invocations (budget : Nat) :
    CallableIndexedOwnedExpressionHeads.SourceInvocationsForWithPost (post := FaultPost functions (registry := registry)) (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation physical selected history emitted
    entry agreement parameterPool parameterRelated _allowed child strict outcome after trace
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact inputs.source_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows
    extension faithful observations functionTypes wellFormed budget child strict trace


include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs extension faithful observations functionTypes in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem native_invocations (budget : Nat) :
    CallableIndexedOwnedExpressionHeads.NativeInvocationsForWithPost (post := FaultPost functions (registry := registry)) (source := source) (context := context)
      (evidence := evidence) (faults := faults) functions owner
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header) bridge initial
      (environment := environment) (ids := ids) budget := by
  intro sourceSize arguments middle middleMap middleWorld middleStore payloads evaluated argumentState
    _argumentRelated _maps _worlds frame _metadata _capture represented _heaps
    origin index metadata administrative actualContext actual ξ frameLocation prefixSize bodyStore value finalStore
    physical selected history emitted prefixRun prefixWithin restored entry parameterPool parameterRelated _allowed child strict
    bodyValue bodyFinalStore completed
  have arity : header.function.parameters.length = arguments.length :=
    (congrArg List.length header.parameters).trans ((List.length_map Prod.fst).trans represented.length.1)
  have sourceAdmission := CallableIndexedOwnedNamedArgumentAdmission.at_successful_arguments header wellFormed
    sourceRuntime covers locals admitted.heap argumentTypes application evaluated.sound arity
  have stable := StableRows.after_administrative (bridge.pool initial) (bridge.pool argumentState) admitted.rows frame
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner (bridge.pool argumentState) header arguments :=
    { origin := origin, index := index, metadata := metadata, administrative := administrative,
      actualContext := actualContext, actual := actual, embedding := ξ, frameLocation := frameLocation,
      physical := physical, selected := selected, history := history, emitted := emitted,
      body := entry, reached := parameterPool, related := parameterRelated, stable := stable,
      heapTyped := sourceAdmission.1, argumentsTyped := sourceAdmission.2 }
  exact inputs.native_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows
    extension faithful observations functionTypes wellFormed budget child strict completed


end Providers

section Heads
variable {functions}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {compilation : SourceCoreFunctions.Context}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (caller : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
    callerProtocol)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate}
  (wellFormed : ProgramWellFormed program) (sourceRuntime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

/-- The admitted outer tuple also retains the exact selected low route. -/
def PreservesHeadAtWithPost (size : Nat) : Prop :=
  ∀ {scope id lowered}, RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers compilation source context evidence certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context node.type outcome reached ∧
        NamedExpressionBodyFaultPostContracts.OuterCallRouteAt
          (functions := functions) (registry := registry) (source := source) (context := context)
          (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
          (FaultPost functions (registry := registry)) owner caller initial
          compilation.administrativePrefix compilation.internalReason size none
          id node lowered outcome after value finalMap finalWorld finalStore

/-- The admitted outer tuple also retains the exact selected low route. -/
def ReflectsHeadAtWithPost (size : Nat) : Prop :=
  ∀ {scope id lowered}, RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers compilation source context evidence certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrative environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) context node.type outcome reached ∧
        NamedExpressionBodyFaultPostContracts.OuterCallRouteAt
          (functions := functions) (registry := registry) (source := source) (context := context)
          (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
          (FaultPost functions (registry := registry)) owner caller initial
          compilation.administrativePrefix compilation.internalReason sourceSize (some size)
          id node lowered outcome after value finalMap finalWorld finalStore

include wellFormed sourceRuntime covers unique sameLayouts extension faithful observations functionTypes owners idsUnique in
/-- Strict actual argument children and a genuine selected static body domain
derive both providers internally, then retain the original reached admission. -/
theorem preserves_head_with_body_post (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (inputs : ∀ {id node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      ∀ header, header ∈ headers → ∀ {callee ids}, node.form = .call callee ids (.declaration header.instantiation) →
      BodyInputs (program := program) (registry := registry) (faults := faults) functions header) :
    PreservesHeadAtWithPost (functions := functions) (registry := registry) (faults := faults)
      (source := source) (context := context) (certificate := certificate) owner caller evidence size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, ⟨reached, related⟩, route⟩ :=
    CallableIndexedOwnedExpressionHeads.preserves_at_with_sequence_with_body_post functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within idsUnique unique owners head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (FaultPost functions (registry := registry))
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact source_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application (inputs found sourceTyped header member form) extension faithful observations functionTypes budget) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame, route⟩


include wellFormed sourceRuntime covers unique sameLayouts extension faithful observations functionTypes in
/-- Strict actual argument children and a genuine selected static body domain
derive both providers internally, then retain the original reached admission. -/
theorem reflects_head_with_body_post (budget size : Nat) (within : size ≤ budget)
    (children : RecursiveNamedBoundedContracts.Below budget
      (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
        (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source certificate faults))
    (inputs : ∀ {id node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      ∀ header, header ∈ headers → ∀ {callee ids}, node.form = .call callee ids (.declaration header.instantiation) →
      BodyInputs (program := program) (registry := registry) (faults := faults) functions header) :
    ReflectsHeadAtWithPost (functions := functions) (registry := registry) (faults := faults)
      (source := source) (context := context) (certificate := certificate) owner caller evidence size := by
  intro scope id lowered head root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, ⟨reached, related⟩, route⟩ :=
    CallableIndexedOwnedExpressionHeads.reflects_at_with_sequence_with_body_post functions owner sameLayouts
      (fun header => CallableIndexedOwnedInvocationBounds.stableOwnerCondition (keys := keys) functions registry header)
      (fun header _ => CallableIndexedOwnedInvocationBounds.stable_owner_authorized functions registry header owner)
      caller budget size within head found initial environments heaps locals agrees typed
      (fun header _member callee ids codes form sequence _nativeTypes _packedType => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, _application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
          (CallableIndexedOwnedIndirectCallerProtocol.forget_slots caller) initial admitted sequence unique argumentTypes
          environments heaps locals agrees typed budget children)
      (FaultPost functions (registry := registry))
      (fun header member callee ids form => by
        obtain ⟨originalTypes, rawResult, predicates, argumentTypes, application⟩ :=
          CallableIndexedOwnedNamedArgumentAdmission.direct_arguments unique found form sourceTyped
        exact native_invocations
          (owner := owner) (functions := functions) caller initial admitted wellFormed sourceRuntime covers locals
          argumentTypes application (inputs found sourceTyped header member form) extension faithful observations functionTypes budget) completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed sourceRuntime covers locals sourceTyped trace frame, route⟩


end Heads

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyPostProviders
