import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds

/-! Supported static lexical bodies supply concrete causal posts at the real
successful argument and parameter state. The existing outer named/direct
producer consumes the same receipt once and retains its full call route. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyPostProviders
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

/-- The actual Header-indexed compiler and child certificates select the
supported lexical grammar. These constructors contain no completed semantics. -/
inductive SupportedInputs (header : CallableIndexedOwnedFunctionValues.Header compiled program) : Prop where
  | discardReturn {expressionSyntax : ExpressionId → Prop}
      {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
      {flow : Expr} {validity : SourceSemantics.Context → Prop}
      (inputs : CallableIndexedOwnedLexicalNamedBodyFaultBounds.BodyInputs
        (functions := functions) (header := header) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax) (flow := flow) validity) :
      SupportedInputs header
  | absent {expressionSyntax : ExpressionId → Prop}
      {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
      {validity : SourceSemantics.Context → Prop}
      {id : StatementId} {node : StatementNode} {binder : TypedBinder}
      {nextContext : SourceSemantics.Context} {rest : List StatementId} {payload : Ty} {suffixFlow : Expr}
      (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts header.owner header.active
        (GenericLexicalStatements.absentRequest header.function.source
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame
        header.globals (compiled.indexed.layouts.allocatorAt header.owner header.active header.onError)
        (GenericLexicalStatements.absentRequest header.function.source
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) binder payload))
      (inputs : CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds.AbsentInputs
        (functions := functions) (header := header) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax) (id := id) (node := node)
        (nextContext := nextContext) (rest := rest) (suffixFlow := suffixFlow) allocation annotation validity) :
      SupportedInputs header

/-- Finite static projections preserve the SAME actual lowering and allocator
receipt. They execute no compiler, expression or flow producer. -/
private theorem SupportedInputs.static_receipt
    {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (inputs : SupportedInputs (registry := registry) (faults := faults) functions header) :
    ∃ (expressionSyntax : ExpressionId → Prop)
      (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (flow : Expr) (validity : SourceSemantics.Context → Prop),
      CallableIndexedOwnedLexicalNamedBodyFaultBounds.StaticBodyInputs
        (functions := functions) (header := header) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax) (flow := flow) validity := by
  cases inputs with
  | @discardReturn expressionSyntax certificates flow validity inputs =>
    exact ⟨expressionSyntax, certificates, flow, validity,
      CallableIndexedOwnedLexicalNamedBodyFaultBounds.BodyInputs.static_inputs functions validity inputs⟩
  | @absent expressionSyntax certificates validity id node binder nextContext rest payload suffixFlow allocation annotation inputs =>
    exact ⟨expressionSyntax, certificates, .letE annotation.expression suffixFlow, validity,
      CallableIndexedOwnedAbsentAllocationNamedBodyFaultBounds.static_inputs
        functions allocation annotation validity inputs⟩

/-- Every supported lexical body retains the same original causal fault post. -/
abbrev FaultPost : BodyFaultPost :=
  ReachedNamedLexicalBodyFaultPaths.model_bodyPost compiled.compatible.checked functions registry

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
  (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys frameLocation current)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed program)

include source rows stable extension faithful observations functionTypes wellFormed in
/-- The shared lexical Tree/finish producer runs once for each genuine strict
body member at this literal parameter state and returned bodyStore. -/
theorem SupportedInputs.source_below
    (inputs : SupportedInputs (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (SourceBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) := by
  obtain ⟨expressionSyntax, certificates, flow, validity, static⟩ :=
    SupportedInputs.static_receipt functions inputs
  intro child _strict
  exact CallableIndexedOwnedLexicalNamedBodyFaultBounds.source_body_with_post.with_static
    functions validity entry reached extension faithful observations functionTypes wellFormed source rows stable static child

include source rows stable extension faithful observations functionTypes wellFormed in
/-- The shared lexical Tree/finish producer runs once for each genuine strict
body member at this literal parameter state and returned bodyStore. -/
theorem SupportedInputs.native_below
    (inputs : SupportedInputs (registry := registry) (faults := faults) functions header)
    (budget : Nat) : RecursiveNamedBoundedContracts.Below budget
      (NativeBodyAtWithPost (FaultPost functions (registry := registry)) (faults := faults) entry reached) := by
  obtain ⟨expressionSyntax, certificates, flow, validity, static⟩ :=
    SupportedInputs.static_receipt functions inputs
  intro child _strict
  exact CallableIndexedOwnedLexicalNamedBodyFaultBounds.native_body_with_post.with_static
    functions validity entry reached extension faithful observations functionTypes wellFormed source rows stable static child

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
  (inputs : SupportedInputs (program := program) (registry := registry) (faults := faults) functions header)
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
  exact inputs.source_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows receipt.stable_owner
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
  exact inputs.native_below receipt.body receipt.reached (receipt.source wellFormed) receipt.rows receipt.stable_owner
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
      SupportedInputs (program := program) (registry := registry) (faults := faults) functions header) :
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
      SupportedInputs (program := program) (registry := registry) (faults := faults) functions header) :
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLexicalNamedBodyPostProviders
