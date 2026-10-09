import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedExpressionRuntimeBounds

/-! Successful arguments construct the original typed parameter receipt.
The strict mixed expression family supplies lexical body children at that
same reached input, retaining their causal post and native prefix route. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyPostProviders
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedAdmittedBodyEntries (SourceReceipt)
open CallableIndexedOwnedInvocationBounds NamedInvocationFaultPostContracts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {flow : Expr}

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
  (validity : SourceSemantics.Context → Prop)
  (inputs : CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.BodyInputs
    (header := header) (certificates := certificates) (expressionSyntax := expressionSyntax) (flow := flow) validity)
  (post : ExpressionFailurePostContracts.ExpressionFaultPost)

include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem source_invocations (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ child, child < outer → ∀ bodyContext, validity bodyContext →
      NamedLexicalFlowFaultPostContracts.ExpressionPreservesAt (post := post) (protocol headers keys)
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness
          (CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.bodyBridge (headers := headers) (keys := keys)))
        program header.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates bodyContext)
        (context := bodyContext) (source := header.function.source) (faults := faults) child)
    :
    CallableIndexedOwnedExpressionHeads.SourceInvocationsForWithPost (post := ReachedNamedLexicalBodyFaultPaths.bodyPost post) (source := source) (context := context)
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
  exact CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.source_below functions validity inputs post
    receipt.body receipt.reached (receipt.source wellFormed) receipt.rows receipt.stable_owner
    outer budget within children child strict trace


include admitted wellFormed sourceRuntime covers locals argumentTypes application inputs in
/-- The original successful arguments supply the exact parameter receipt;
only the concrete strict body producer is invoked. -/
theorem native_invocations (outer budget : Nat) (within : budget ≤ outer)
    (children : ∀ child, child < outer → ∀ bodyContext, validity bodyContext →
      NamedLexicalFlowFaultPostContracts.ExpressionReflectsAt (post := post) (protocol headers keys)
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness
          (CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.bodyBridge (headers := headers) (keys := keys)))
        program header.function.evidence (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (ProtectedStateLexicalSourceSites.ExpressionFacts header.function.source) (certificates bodyContext)
        (context := bodyContext) (source := header.function.source) (faults := faults) child)
    :
    CallableIndexedOwnedExpressionHeads.NativeInvocationsForWithPost (post := ReachedNamedLexicalBodyFaultPaths.bodyPost post) (source := source) (context := context)
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
  exact CallableIndexedOwnedMixedLexicalNamedBodyFaultBounds.native_below functions validity inputs post
    receipt.body receipt.reached (receipt.source wellFormed) receipt.rows receipt.stable_owner
    outer budget within children child strict completed


end Providers

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMixedLexicalNamedBodyPostProviders
